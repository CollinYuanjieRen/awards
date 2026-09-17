import MerLeanExperiment.Certificates.FixedCore1.Inputs

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c5881 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5881 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4749, some c5500, some c5525, some c4872, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p5881 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5881 : lratChecker f5881 p5881 = .success := by decide +kernel
theorem unsat5881 : Unsatisfiable (PosFin 65) f5881 := by
  apply lratCheckerSound f5881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5881
  · intro a ha; simp [p5881] at ha; subst a; trivial
  · exact checked5881
theorem derived5881 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5881 := by
  apply localUnsat_implies_entails f5881 [c4749, c5500, c5525, c4872] c5881 unsat5881 (by rfl) a
  have h0 : Entails.eval a c4749 := h 4748 (by decide)
  have h1 : Entails.eval a c5500 := h 5499 (by decide)
  have h2 : Entails.eval a c5525 := h 5524 (by decide)
  have h3 : Entails.eval a c4872 := h 4871 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5882 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5882 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5020, some c5478, some c5154, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p5882 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5882 : lratChecker f5882 p5882 = .success := by decide +kernel
theorem unsat5882 : Unsatisfiable (PosFin 65) f5882 := by
  apply lratCheckerSound f5882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5882
  · intro a ha; simp [p5882] at ha; subst a; trivial
  · exact checked5882
theorem derived5882 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5882 := by
  apply localUnsat_implies_entails f5882 [c5020, c5478, c5154] c5882 unsat5882 (by rfl) a
  have h0 : Entails.eval a c5020 := h 5019 (by decide)
  have h1 : Entails.eval a c5478 := h 5477 (by decide)
  have h2 : Entails.eval a c5154 := h 5153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5883 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, false), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5883 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3998, some c4921, some c4943, some c4324, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p5883 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5883 : lratChecker f5883 p5883 = .success := by decide +kernel
theorem unsat5883 : Unsatisfiable (PosFin 65) f5883 := by
  apply lratCheckerSound f5883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5883
  · intro a ha; simp [p5883] at ha; subst a; trivial
  · exact checked5883
theorem derived5883 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5883 := by
  apply localUnsat_implies_entails f5883 [c3998, c4921, c4943, c4324] c5883 unsat5883 (by rfl) a
  have h0 : Entails.eval a c3998 := h 3997 (by decide)
  have h1 : Entails.eval a c4921 := h 4920 (by decide)
  have h2 : Entails.eval a c4943 := h 4942 (by decide)
  have h3 : Entails.eval a c4324 := h 4323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5884 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨48, by decide⟩, true), (⟨34, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5884 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4212, some c4283, some c5741, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5884 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5884 : lratChecker f5884 p5884 = .success := by decide +kernel
theorem unsat5884 : Unsatisfiable (PosFin 65) f5884 := by
  apply lratCheckerSound f5884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5884
  · intro a ha; simp [p5884] at ha; subst a; trivial
  · exact checked5884
theorem derived5884 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5884 := by
  apply localUnsat_implies_entails f5884 [c4212, c4283, c5741] c5884 unsat5884 (by rfl) a
  have h0 : Entails.eval a c4212 := h 4211 (by decide)
  have h1 : Entails.eval a c4283 := h 4282 (by decide)
  have h2 : Entails.eval a c5741 := h 5740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5885 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5885 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5305, some c5331, some c4988, some c5221, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5885 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5885 : lratChecker f5885 p5885 = .success := by decide +kernel
theorem unsat5885 : Unsatisfiable (PosFin 65) f5885 := by
  apply lratCheckerSound f5885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5885
  · intro a ha; simp [p5885] at ha; subst a; trivial
  · exact checked5885
theorem derived5885 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5885 := by
  apply localUnsat_implies_entails f5885 [c5305, c5331, c4988, c5221] c5885 unsat5885 (by rfl) a
  have h0 : Entails.eval a c5305 := h 5304 (by decide)
  have h1 : Entails.eval a c5331 := h 5330 (by decide)
  have h2 : Entails.eval a c4988 := h 4987 (by decide)
  have h3 : Entails.eval a c5221 := h 5220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5886 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨34, by decide⟩, true), (⟨52, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5886 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5885, some c4081, some c3967, some c4482, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5886 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5886 : lratChecker f5886 p5886 = .success := by decide +kernel
theorem unsat5886 : Unsatisfiable (PosFin 65) f5886 := by
  apply lratCheckerSound f5886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5886
  · intro a ha; simp [p5886] at ha; subst a; trivial
  · exact checked5886
theorem derived5886 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5886 := by
  apply localUnsat_implies_entails f5886 [c5885, c4081, c3967, c4482] c5886 unsat5886 (by rfl) a
  have h0 : Entails.eval a c5885 := derived5885 a h
  have h1 : Entails.eval a c4081 := h 4080 (by decide)
  have h2 : Entails.eval a c3967 := h 3966 (by decide)
  have h3 : Entails.eval a c4482 := h 4481 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5887 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨58, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5887 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3814, some c3844, some c3469, some c4245, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5887 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5887 : lratChecker f5887 p5887 = .success := by decide +kernel
theorem unsat5887 : Unsatisfiable (PosFin 65) f5887 := by
  apply lratCheckerSound f5887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5887
  · intro a ha; simp [p5887] at ha; subst a; trivial
  · exact checked5887
theorem derived5887 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5887 := by
  apply localUnsat_implies_entails f5887 [c3814, c3844, c3469, c4245] c5887 unsat5887 (by rfl) a
  have h0 : Entails.eval a c3814 := h 3813 (by decide)
  have h1 : Entails.eval a c3844 := h 3843 (by decide)
  have h2 : Entails.eval a c3469 := h 3468 (by decide)
  have h3 : Entails.eval a c4245 := h 4244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5888 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨47, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5888 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3623, some c3899, some c5096, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p5888 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5888 : lratChecker f5888 p5888 = .success := by decide +kernel
theorem unsat5888 : Unsatisfiable (PosFin 65) f5888 := by
  apply lratCheckerSound f5888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5888
  · intro a ha; simp [p5888] at ha; subst a; trivial
  · exact checked5888
theorem derived5888 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5888 := by
  apply localUnsat_implies_entails f5888 [c3623, c3899, c5096] c5888 unsat5888 (by rfl) a
  have h0 : Entails.eval a c3623 := h 3622 (by decide)
  have h1 : Entails.eval a c3899 := h 3898 (by decide)
  have h2 : Entails.eval a c5096 := h 5095 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5889 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨58, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5889 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5888, some c5887, some c4548, some c4486, some c3516, some c3542, some c4869, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5889 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked5889 : lratChecker f5889 p5889 = .success := by decide +kernel
theorem unsat5889 : Unsatisfiable (PosFin 65) f5889 := by
  apply lratCheckerSound f5889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5889
  · intro a ha; simp [p5889] at ha; subst a; trivial
  · exact checked5889
theorem derived5889 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5889 := by
  apply localUnsat_implies_entails f5889 [c5888, c5887, c4548, c4486, c3516, c3542, c4869] c5889 unsat5889 (by rfl) a
  have h0 : Entails.eval a c5888 := derived5888 a h
  have h1 : Entails.eval a c5887 := derived5887 a h
  have h2 : Entails.eval a c4548 := h 4547 (by decide)
  have h3 : Entails.eval a c4486 := h 4485 (by decide)
  have h4 : Entails.eval a c3516 := h 3515 (by decide)
  have h5 : Entails.eval a c3542 := h 3541 (by decide)
  have h6 : Entails.eval a c4869 := h 4868 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5890 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨41, by decide⟩, true), (⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5890 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5853, some c5827, some c5748, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p5890 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5890 : lratChecker f5890 p5890 = .success := by decide +kernel
theorem unsat5890 : Unsatisfiable (PosFin 65) f5890 := by
  apply lratCheckerSound f5890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5890
  · intro a ha; simp [p5890] at ha; subst a; trivial
  · exact checked5890
theorem derived5890 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5890 := by
  apply localUnsat_implies_entails f5890 [c5853, c5827, c5748] c5890 unsat5890 (by rfl) a
  have h0 : Entails.eval a c5853 := h 5852 (by decide)
  have h1 : Entails.eval a c5827 := h 5826 (by decide)
  have h2 : Entails.eval a c5748 := h 5747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5891 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨58, by decide⟩, false), (⟨55, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5891 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4311, some c5433, some c5829, some c4086, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p5891 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5891 : lratChecker f5891 p5891 = .success := by decide +kernel
theorem unsat5891 : Unsatisfiable (PosFin 65) f5891 := by
  apply lratCheckerSound f5891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5891
  · intro a ha; simp [p5891] at ha; subst a; trivial
  · exact checked5891
theorem derived5891 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5891 := by
  apply localUnsat_implies_entails f5891 [c4311, c5433, c5829, c4086] c5891 unsat5891 (by rfl) a
  have h0 : Entails.eval a c4311 := h 4310 (by decide)
  have h1 : Entails.eval a c5433 := h 5432 (by decide)
  have h2 : Entails.eval a c5829 := h 5828 (by decide)
  have h3 : Entails.eval a c4086 := h 4085 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5892 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨47, by decide⟩, true), (⟨58, by decide⟩, false), (⟨55, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5892 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3626, some c3753, some c3903, some c5101, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p5892 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5892 : lratChecker f5892 p5892 = .success := by decide +kernel
theorem unsat5892 : Unsatisfiable (PosFin 65) f5892 := by
  apply lratCheckerSound f5892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5892
  · intro a ha; simp [p5892] at ha; subst a; trivial
  · exact checked5892
theorem derived5892 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5892 := by
  apply localUnsat_implies_entails f5892 [c3626, c3753, c3903, c5101] c5892 unsat5892 (by rfl) a
  have h0 : Entails.eval a c3626 := h 3625 (by decide)
  have h1 : Entails.eval a c3753 := h 3752 (by decide)
  have h2 : Entails.eval a c3903 := h 3902 (by decide)
  have h3 : Entails.eval a c5101 := h 5100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5893 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5893 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4995, some c5104, some c5076, some c5421, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5893 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5893 : lratChecker f5893 p5893 = .success := by decide +kernel
theorem unsat5893 : Unsatisfiable (PosFin 65) f5893 := by
  apply lratCheckerSound f5893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5893
  · intro a ha; simp [p5893] at ha; subst a; trivial
  · exact checked5893
theorem derived5893 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5893 := by
  apply localUnsat_implies_entails f5893 [c4995, c5104, c5076, c5421] c5893 unsat5893 (by rfl) a
  have h0 : Entails.eval a c4995 := h 4994 (by decide)
  have h1 : Entails.eval a c5104 := h 5103 (by decide)
  have h2 : Entails.eval a c5076 := h 5075 (by decide)
  have h3 : Entails.eval a c5421 := h 5420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5894 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨40, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5894 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5723, some c4513, some c5338, some c4439, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5894 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5894 : lratChecker f5894 p5894 = .success := by decide +kernel
theorem unsat5894 : Unsatisfiable (PosFin 65) f5894 := by
  apply lratCheckerSound f5894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5894
  · intro a ha; simp [p5894] at ha; subst a; trivial
  · exact checked5894
theorem derived5894 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5894 := by
  apply localUnsat_implies_entails f5894 [c5723, c4513, c5338, c4439] c5894 unsat5894 (by rfl) a
  have h0 : Entails.eval a c5723 := h 5722 (by decide)
  have h1 : Entails.eval a c4513 := h 4512 (by decide)
  have h2 : Entails.eval a c5338 := h 5337 (by decide)
  have h3 : Entails.eval a c4439 := h 4438 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5895 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5895 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5893, some c5894, some c5227, some c3602, some c4066, some c3502, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5895 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked5895 : lratChecker f5895 p5895 = .success := by decide +kernel
theorem unsat5895 : Unsatisfiable (PosFin 65) f5895 := by
  apply lratCheckerSound f5895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5895
  · intro a ha; simp [p5895] at ha; subst a; trivial
  · exact checked5895
theorem derived5895 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5895 := by
  apply localUnsat_implies_entails f5895 [c5893, c5894, c5227, c3602, c4066, c3502] c5895 unsat5895 (by rfl) a
  have h0 : Entails.eval a c5893 := derived5893 a h
  have h1 : Entails.eval a c5894 := derived5894 a h
  have h2 : Entails.eval a c5227 := h 5226 (by decide)
  have h3 : Entails.eval a c3602 := h 3601 (by decide)
  have h4 : Entails.eval a c4066 := h 4065 (by decide)
  have h5 : Entails.eval a c3502 := h 3501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5896 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5896 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5227, some c3602, some c4066, some c3502, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5896 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5896 : lratChecker f5896 p5896 = .success := by decide +kernel
theorem unsat5896 : Unsatisfiable (PosFin 65) f5896 := by
  apply lratCheckerSound f5896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5896
  · intro a ha; simp [p5896] at ha; subst a; trivial
  · exact checked5896
theorem derived5896 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5896 := by
  apply localUnsat_implies_entails f5896 [c5227, c3602, c4066, c3502] c5896 unsat5896 (by rfl) a
  have h0 : Entails.eval a c5227 := h 5226 (by decide)
  have h1 : Entails.eval a c3602 := h 3601 (by decide)
  have h2 : Entails.eval a c4066 := h 4065 (by decide)
  have h3 : Entails.eval a c3502 := h 3501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5897 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5897 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4316, some c3502, some c3632, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5897 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5897 : lratChecker f5897 p5897 = .success := by decide +kernel
theorem unsat5897 : Unsatisfiable (PosFin 65) f5897 := by
  apply lratCheckerSound f5897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5897
  · intro a ha; simp [p5897] at ha; subst a; trivial
  · exact checked5897
theorem derived5897 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5897 := by
  apply localUnsat_implies_entails f5897 [c4316, c3502, c3632] c5897 unsat5897 (by rfl) a
  have h0 : Entails.eval a c4316 := h 4315 (by decide)
  have h1 : Entails.eval a c3502 := h 3501 (by decide)
  have h2 : Entails.eval a c3632 := h 3631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5898 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5898 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4689, some c4395, some c4353, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5898 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5898 : lratChecker f5898 p5898 = .success := by decide +kernel
theorem unsat5898 : Unsatisfiable (PosFin 65) f5898 := by
  apply lratCheckerSound f5898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5898
  · intro a ha; simp [p5898] at ha; subst a; trivial
  · exact checked5898
theorem derived5898 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5898 := by
  apply localUnsat_implies_entails f5898 [c4689, c4395, c4353] c5898 unsat5898 (by rfl) a
  have h0 : Entails.eval a c4689 := h 4688 (by decide)
  have h1 : Entails.eval a c4395 := h 4394 (by decide)
  have h2 : Entails.eval a c4353 := h 4352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5899 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5899 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5895, some c5896, some c5898, some c5897, some c4205, some c4171, some c3946, some c4593, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5899 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked5899 : lratChecker f5899 p5899 = .success := by decide +kernel
theorem unsat5899 : Unsatisfiable (PosFin 65) f5899 := by
  apply lratCheckerSound f5899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5899
  · intro a ha; simp [p5899] at ha; subst a; trivial
  · exact checked5899
theorem derived5899 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5899 := by
  apply localUnsat_implies_entails f5899 [c5895, c5896, c5898, c5897, c4205, c4171, c3946, c4593] c5899 unsat5899 (by rfl) a
  have h0 : Entails.eval a c5895 := derived5895 a h
  have h1 : Entails.eval a c5896 := derived5896 a h
  have h2 : Entails.eval a c5898 := derived5898 a h
  have h3 : Entails.eval a c5897 := derived5897 a h
  have h4 : Entails.eval a c4205 := h 4204 (by decide)
  have h5 : Entails.eval a c4171 := h 4170 (by decide)
  have h6 : Entails.eval a c3946 := h 3945 (by decide)
  have h7 : Entails.eval a c4593 := h 4592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5900 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5900 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5045, some c5197, some c5255, some c5523, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p5900 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5900 : lratChecker f5900 p5900 = .success := by decide +kernel
theorem unsat5900 : Unsatisfiable (PosFin 65) f5900 := by
  apply lratCheckerSound f5900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5900
  · intro a ha; simp [p5900] at ha; subst a; trivial
  · exact checked5900
theorem derived5900 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5900 := by
  apply localUnsat_implies_entails f5900 [c5045, c5197, c5255, c5523] c5900 unsat5900 (by rfl) a
  have h0 : Entails.eval a c5045 := h 5044 (by decide)
  have h1 : Entails.eval a c5197 := h 5196 (by decide)
  have h2 : Entails.eval a c5255 := h 5254 (by decide)
  have h3 : Entails.eval a c5523 := h 5522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5901 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5901 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5895, some c5899, some c5900, some c5644, some c4202, some c3796, some c3478, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5901 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked5901 : lratChecker f5901 p5901 = .success := by decide +kernel
theorem unsat5901 : Unsatisfiable (PosFin 65) f5901 := by
  apply lratCheckerSound f5901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5901
  · intro a ha; simp [p5901] at ha; subst a; trivial
  · exact checked5901
theorem derived5901 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5901 := by
  apply localUnsat_implies_entails f5901 [c5895, c5899, c5900, c5644, c4202, c3796, c3478] c5901 unsat5901 (by rfl) a
  have h0 : Entails.eval a c5895 := derived5895 a h
  have h1 : Entails.eval a c5899 := derived5899 a h
  have h2 : Entails.eval a c5900 := derived5900 a h
  have h3 : Entails.eval a c5644 := h 5643 (by decide)
  have h4 : Entails.eval a c4202 := h 4201 (by decide)
  have h5 : Entails.eval a c3796 := h 3795 (by decide)
  have h6 : Entails.eval a c3478 := h 3477 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5902 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨48, by decide⟩, true), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5902 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5644, some c3796, some c3478, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5902 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5902 : lratChecker f5902 p5902 = .success := by decide +kernel
theorem unsat5902 : Unsatisfiable (PosFin 65) f5902 := by
  apply lratCheckerSound f5902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5902
  · intro a ha; simp [p5902] at ha; subst a; trivial
  · exact checked5902
theorem derived5902 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5902 := by
  apply localUnsat_implies_entails f5902 [c5644, c3796, c3478] c5902 unsat5902 (by rfl) a
  have h0 : Entails.eval a c5644 := h 5643 (by decide)
  have h1 : Entails.eval a c3796 := h 3795 (by decide)
  have h2 : Entails.eval a c3478 := h 3477 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5903 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨48, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5903 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5902, some c4995, some c5359, some c3677, some c3478, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5903 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5903 : lratChecker f5903 p5903 = .success := by decide +kernel
theorem unsat5903 : Unsatisfiable (PosFin 65) f5903 := by
  apply lratCheckerSound f5903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5903
  · intro a ha; simp [p5903] at ha; subst a; trivial
  · exact checked5903
theorem derived5903 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5903 := by
  apply localUnsat_implies_entails f5903 [c5902, c4995, c5359, c3677, c3478] c5903 unsat5903 (by rfl) a
  have h0 : Entails.eval a c5902 := derived5902 a h
  have h1 : Entails.eval a c4995 := h 4994 (by decide)
  have h2 : Entails.eval a c5359 := h 5358 (by decide)
  have h3 : Entails.eval a c3677 := h 3676 (by decide)
  have h4 : Entails.eval a c3478 := h 3477 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5904 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨37, by decide⟩, false), (⟨63, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5904 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5903, some c4205, some c4106, some c4995, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p5904 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5904 : lratChecker f5904 p5904 = .success := by decide +kernel
theorem unsat5904 : Unsatisfiable (PosFin 65) f5904 := by
  apply lratCheckerSound f5904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5904
  · intro a ha; simp [p5904] at ha; subst a; trivial
  · exact checked5904
theorem derived5904 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5904 := by
  apply localUnsat_implies_entails f5904 [c5903, c4205, c4106, c4995] c5904 unsat5904 (by rfl) a
  have h0 : Entails.eval a c5903 := derived5903 a h
  have h1 : Entails.eval a c4205 := h 4204 (by decide)
  have h2 : Entails.eval a c4106 := h 4105 (by decide)
  have h3 : Entails.eval a c4995 := h 4994 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5905 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨52, by decide⟩, true), (⟨34, by decide⟩, true), (⟨46, by decide⟩, true), (⟨38, by decide⟩, true), (⟨57, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5905 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4080, some c4275, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p5905 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5905 : lratChecker f5905 p5905 = .success := by decide +kernel
theorem unsat5905 : Unsatisfiable (PosFin 65) f5905 := by
  apply lratCheckerSound f5905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5905
  · intro a ha; simp [p5905] at ha; subst a; trivial
  · exact checked5905
theorem derived5905 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5905 := by
  apply localUnsat_implies_entails f5905 [c4080, c4275] c5905 unsat5905 (by rfl) a
  have h0 : Entails.eval a c4080 := h 4079 (by decide)
  have h1 : Entails.eval a c4275 := h 4274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5906 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5906 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5901, some c5904, some c5048, some c5256, some c3713, some c4472, some c3527, some c4747, some c4779, some c4995, some c4513, some c3505, some c5886, some c5905, some c4480, some c5683, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5906 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked5906 : lratChecker f5906 p5906 = .success := by decide +kernel
theorem unsat5906 : Unsatisfiable (PosFin 65) f5906 := by
  apply lratCheckerSound f5906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5906
  · intro a ha; simp [p5906] at ha; subst a; trivial
  · exact checked5906
theorem derived5906 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5906 := by
  apply localUnsat_implies_entails f5906 [c5901, c5904, c5048, c5256, c3713, c4472, c3527, c4747, c4779, c4995, c4513, c3505, c5886, c5905, c4480, c5683] c5906 unsat5906 (by rfl) a
  have h0 : Entails.eval a c5901 := derived5901 a h
  have h1 : Entails.eval a c5904 := derived5904 a h
  have h2 : Entails.eval a c5048 := h 5047 (by decide)
  have h3 : Entails.eval a c5256 := h 5255 (by decide)
  have h4 : Entails.eval a c3713 := h 3712 (by decide)
  have h5 : Entails.eval a c4472 := h 4471 (by decide)
  have h6 : Entails.eval a c3527 := h 3526 (by decide)
  have h7 : Entails.eval a c4747 := h 4746 (by decide)
  have h8 : Entails.eval a c4779 := h 4778 (by decide)
  have h9 : Entails.eval a c4995 := h 4994 (by decide)
  have h10 : Entails.eval a c4513 := h 4512 (by decide)
  have h11 : Entails.eval a c3505 := h 3504 (by decide)
  have h12 : Entails.eval a c5886 := derived5886 a h
  have h13 : Entails.eval a c5905 := derived5905 a h
  have h14 : Entails.eval a c4480 := h 4479 (by decide)
  have h15 : Entails.eval a c5683 := h 5682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5907 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨37, by decide⟩, true), (⟨63, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5907 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4066, some c3950, some c4036, some c4571, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p5907 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5907 : lratChecker f5907 p5907 = .success := by decide +kernel
theorem unsat5907 : Unsatisfiable (PosFin 65) f5907 := by
  apply lratCheckerSound f5907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5907
  · intro a ha; simp [p5907] at ha; subst a; trivial
  · exact checked5907
theorem derived5907 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5907 := by
  apply localUnsat_implies_entails f5907 [c4066, c3950, c4036, c4571] c5907 unsat5907 (by rfl) a
  have h0 : Entails.eval a c4066 := h 4065 (by decide)
  have h1 : Entails.eval a c3950 := h 3949 (by decide)
  have h2 : Entails.eval a c4036 := h 4035 (by decide)
  have h3 : Entails.eval a c4571 := h 4570 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5908 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5908 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4353, some c4571, some c4662, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5908 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5908 : lratChecker f5908 p5908 = .success := by decide +kernel
theorem unsat5908 : Unsatisfiable (PosFin 65) f5908 := by
  apply lratCheckerSound f5908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5908
  · intro a ha; simp [p5908] at ha; subst a; trivial
  · exact checked5908
theorem derived5908 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5908 := by
  apply localUnsat_implies_entails f5908 [c4353, c4571, c4662] c5908 unsat5908 (by rfl) a
  have h0 : Entails.eval a c4353 := h 4352 (by decide)
  have h1 : Entails.eval a c4571 := h 4570 (by decide)
  have h2 : Entails.eval a c4662 := h 4661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5909 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5909 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3625, some c4005, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p5909 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5909 : lratChecker f5909 p5909 = .success := by decide +kernel
theorem unsat5909 : Unsatisfiable (PosFin 65) f5909 := by
  apply lratCheckerSound f5909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5909
  · intro a ha; simp [p5909] at ha; subst a; trivial
  · exact checked5909
theorem derived5909 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5909 := by
  apply localUnsat_implies_entails f5909 [c3625, c4005] c5909 unsat5909 (by rfl) a
  have h0 : Entails.eval a c3625 := h 3624 (by decide)
  have h1 : Entails.eval a c4005 := h 4004 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5910 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f5910 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4630, some c5587, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p5910 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5910 : lratChecker f5910 p5910 = .success := by decide +kernel
theorem unsat5910 : Unsatisfiable (PosFin 65) f5910 := by
  apply lratCheckerSound f5910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5910
  · intro a ha; simp [p5910] at ha; subst a; trivial
  · exact checked5910
theorem derived5910 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5910 := by
  apply localUnsat_implies_entails f5910 [c4630, c5587] c5910 unsat5910 (by rfl) a
  have h0 : Entails.eval a c4630 := h 4629 (by decide)
  have h1 : Entails.eval a c5587 := h 5586 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5911 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5911 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5906, some c5907, some c5901, some c4398, some c3505, some c4295, some c3713, some c3654, some c4129, some c5312, some c5644, some c4809, some c5909, some c5910, some c4141, some c5613, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5911 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked5911 : lratChecker f5911 p5911 = .success := by decide +kernel
theorem unsat5911 : Unsatisfiable (PosFin 65) f5911 := by
  apply lratCheckerSound f5911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5911
  · intro a ha; simp [p5911] at ha; subst a; trivial
  · exact checked5911
theorem derived5911 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5911 := by
  apply localUnsat_implies_entails f5911 [c5906, c5907, c5901, c4398, c3505, c4295, c3713, c3654, c4129, c5312, c5644, c4809, c5909, c5910, c4141, c5613] c5911 unsat5911 (by rfl) a
  have h0 : Entails.eval a c5906 := derived5906 a h
  have h1 : Entails.eval a c5907 := derived5907 a h
  have h2 : Entails.eval a c5901 := derived5901 a h
  have h3 : Entails.eval a c4398 := h 4397 (by decide)
  have h4 : Entails.eval a c3505 := h 3504 (by decide)
  have h5 : Entails.eval a c4295 := h 4294 (by decide)
  have h6 : Entails.eval a c3713 := h 3712 (by decide)
  have h7 : Entails.eval a c3654 := h 3653 (by decide)
  have h8 : Entails.eval a c4129 := h 4128 (by decide)
  have h9 : Entails.eval a c5312 := h 5311 (by decide)
  have h10 : Entails.eval a c5644 := h 5643 (by decide)
  have h11 : Entails.eval a c4809 := h 4808 (by decide)
  have h12 : Entails.eval a c5909 := derived5909 a h
  have h13 : Entails.eval a c5910 := derived5910 a h
  have h14 : Entails.eval a c4141 := h 4140 (by decide)
  have h15 : Entails.eval a c5613 := h 5612 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5912 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5912 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5906, some c5907, some c5911, some c5908, some c5227, some c3602, some c3505, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5912 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked5912 : lratChecker f5912 p5912 = .success := by decide +kernel
theorem unsat5912 : Unsatisfiable (PosFin 65) f5912 := by
  apply lratCheckerSound f5912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5912
  · intro a ha; simp [p5912] at ha; subst a; trivial
  · exact checked5912
theorem derived5912 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5912 := by
  apply localUnsat_implies_entails f5912 [c5906, c5907, c5911, c5908, c5227, c3602, c3505] c5912 unsat5912 (by rfl) a
  have h0 : Entails.eval a c5906 := derived5906 a h
  have h1 : Entails.eval a c5907 := derived5907 a h
  have h2 : Entails.eval a c5911 := derived5911 a h
  have h3 : Entails.eval a c5908 := derived5908 a h
  have h4 : Entails.eval a c5227 := h 5226 (by decide)
  have h5 : Entails.eval a c3602 := h 3601 (by decide)
  have h6 : Entails.eval a c3505 := h 3504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5913 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨37, by decide⟩, true), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5913 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5907, some c3505, some c3452, some c4691, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5913 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5913 : lratChecker f5913 p5913 = .success := by decide +kernel
theorem unsat5913 : Unsatisfiable (PosFin 65) f5913 := by
  apply lratCheckerSound f5913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5913
  · intro a ha; simp [p5913] at ha; subst a; trivial
  · exact checked5913
theorem derived5913 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5913 := by
  apply localUnsat_implies_entails f5913 [c5907, c3505, c3452, c4691] c5913 unsat5913 (by rfl) a
  have h0 : Entails.eval a c5907 := derived5907 a h
  have h1 : Entails.eval a c3505 := h 3504 (by decide)
  have h2 : Entails.eval a c3452 := h 3451 (by decide)
  have h3 : Entails.eval a c4691 := h 4690 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5914 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5914 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4009, some c4013, some c4308, some c4138, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5914 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5914 : lratChecker f5914 p5914 = .success := by decide +kernel
theorem unsat5914 : Unsatisfiable (PosFin 65) f5914 := by
  apply lratCheckerSound f5914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5914
  · intro a ha; simp [p5914] at ha; subst a; trivial
  · exact checked5914
theorem derived5914 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5914 := by
  apply localUnsat_implies_entails f5914 [c4009, c4013, c4308, c4138] c5914 unsat5914 (by rfl) a
  have h0 : Entails.eval a c4009 := h 4008 (by decide)
  have h1 : Entails.eval a c4013 := h 4012 (by decide)
  have h2 : Entails.eval a c4308 := h 4307 (by decide)
  have h3 : Entails.eval a c4138 := h 4137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5915 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5915 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5907, some c5913, some c3602, some c5908, some c4398, some c4295, some c4440, some c4472, some c5312, some c5370, some c4129, some c4809, some c5914, some c3630, some c3634, some c5660, some c3618, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5915 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked5915 : lratChecker f5915 p5915 = .success := by decide +kernel
theorem unsat5915 : Unsatisfiable (PosFin 65) f5915 := by
  apply lratCheckerSound f5915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5915
  · intro a ha; simp [p5915] at ha; subst a; trivial
  · exact checked5915
theorem derived5915 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5915 := by
  apply localUnsat_implies_entails f5915 [c5907, c5913, c3602, c5908, c4398, c4295, c4440, c4472, c5312, c5370, c4129, c4809, c5914, c3630, c3634, c5660, c3618] c5915 unsat5915 (by rfl) a
  have h0 : Entails.eval a c5907 := derived5907 a h
  have h1 : Entails.eval a c5913 := derived5913 a h
  have h2 : Entails.eval a c3602 := h 3601 (by decide)
  have h3 : Entails.eval a c5908 := derived5908 a h
  have h4 : Entails.eval a c4398 := h 4397 (by decide)
  have h5 : Entails.eval a c4295 := h 4294 (by decide)
  have h6 : Entails.eval a c4440 := h 4439 (by decide)
  have h7 : Entails.eval a c4472 := h 4471 (by decide)
  have h8 : Entails.eval a c5312 := h 5311 (by decide)
  have h9 : Entails.eval a c5370 := h 5369 (by decide)
  have h10 : Entails.eval a c4129 := h 4128 (by decide)
  have h11 : Entails.eval a c4809 := h 4808 (by decide)
  have h12 : Entails.eval a c5914 := derived5914 a h
  have h13 : Entails.eval a c3630 := h 3629 (by decide)
  have h14 : Entails.eval a c3634 := h 3633 (by decide)
  have h15 : Entails.eval a c5660 := h 5659 (by decide)
  have h16 : Entails.eval a c3618 := h 3617 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5916 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, false), (⟨39, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f5916 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5539, some c3836, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p5916 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5916 : lratChecker f5916 p5916 = .success := by decide +kernel
theorem unsat5916 : Unsatisfiable (PosFin 65) f5916 := by
  apply lratCheckerSound f5916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5916
  · intro a ha; simp [p5916] at ha; subst a; trivial
  · exact checked5916
theorem derived5916 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5916 := by
  apply localUnsat_implies_entails f5916 [c5539, c3836] c5916 unsat5916 (by rfl) a
  have h0 : Entails.eval a c5539 := h 5538 (by decide)
  have h1 : Entails.eval a c3836 := h 3835 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5917 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5917 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5912, some c5915, some c5904, some c5048, some c5256, some c4472, some c3713, some c3556, some c4378, some c4747, some c4779, some c4995, some c4513, some c3505, some c4705, some c5886, some c5916, some c4485, some c4244, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5917 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked5917 : lratChecker f5917 p5917 = .success := by decide +kernel
theorem unsat5917 : Unsatisfiable (PosFin 65) f5917 := by
  apply lratCheckerSound f5917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5917
  · intro a ha; simp [p5917] at ha; subst a; trivial
  · exact checked5917
theorem derived5917 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5917 := by
  apply localUnsat_implies_entails f5917 [c5912, c5915, c5904, c5048, c5256, c4472, c3713, c3556, c4378, c4747, c4779, c4995, c4513, c3505, c4705, c5886, c5916, c4485, c4244] c5917 unsat5917 (by rfl) a
  have h0 : Entails.eval a c5912 := derived5912 a h
  have h1 : Entails.eval a c5915 := derived5915 a h
  have h2 : Entails.eval a c5904 := derived5904 a h
  have h3 : Entails.eval a c5048 := h 5047 (by decide)
  have h4 : Entails.eval a c5256 := h 5255 (by decide)
  have h5 : Entails.eval a c4472 := h 4471 (by decide)
  have h6 : Entails.eval a c3713 := h 3712 (by decide)
  have h7 : Entails.eval a c3556 := h 3555 (by decide)
  have h8 : Entails.eval a c4378 := h 4377 (by decide)
  have h9 : Entails.eval a c4747 := h 4746 (by decide)
  have h10 : Entails.eval a c4779 := h 4778 (by decide)
  have h11 : Entails.eval a c4995 := h 4994 (by decide)
  have h12 : Entails.eval a c4513 := h 4512 (by decide)
  have h13 : Entails.eval a c3505 := h 3504 (by decide)
  have h14 : Entails.eval a c4705 := h 4704 (by decide)
  have h15 : Entails.eval a c5886 := derived5886 a h
  have h16 : Entails.eval a c5916 := derived5916 a h
  have h17 : Entails.eval a c4485 := h 4484 (by decide)
  have h18 : Entails.eval a c4244 := h 4243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5918 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5918 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4485, some c4244, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5918 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5918 : lratChecker f5918 p5918 = .success := by decide +kernel
theorem unsat5918 : Unsatisfiable (PosFin 65) f5918 := by
  apply lratCheckerSound f5918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5918
  · intro a ha; simp [p5918] at ha; subst a; trivial
  · exact checked5918
theorem derived5918 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5918 := by
  apply localUnsat_implies_entails f5918 [c4485, c4244] c5918 unsat5918 (by rfl) a
  have h0 : Entails.eval a c4485 := h 4484 (by decide)
  have h1 : Entails.eval a c4244 := h 4243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5919 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨58, by decide⟩, false), (⟨46, by decide⟩, true), (⟨52, by decide⟩, true), (⟨34, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5919 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4272, some c4275, some c4262, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5919 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5919 : lratChecker f5919 p5919 = .success := by decide +kernel
theorem unsat5919 : Unsatisfiable (PosFin 65) f5919 := by
  apply lratCheckerSound f5919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5919
  · intro a ha; simp [p5919] at ha; subst a; trivial
  · exact checked5919
theorem derived5919 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5919 := by
  apply localUnsat_implies_entails f5919 [c4272, c4275, c4262] c5919 unsat5919 (by rfl) a
  have h0 : Entails.eval a c4272 := h 4271 (by decide)
  have h1 : Entails.eval a c4275 := h 4274 (by decide)
  have h2 : Entails.eval a c4262 := h 4261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5920 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨40, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5920 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4485, some c3813, some c4244, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5920 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5920 : lratChecker f5920 p5920 = .success := by decide +kernel
theorem unsat5920 : Unsatisfiable (PosFin 65) f5920 := by
  apply lratCheckerSound f5920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5920
  · intro a ha; simp [p5920] at ha; subst a; trivial
  · exact checked5920
theorem derived5920 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5920 := by
  apply localUnsat_implies_entails f5920 [c4485, c3813, c4244] c5920 unsat5920 (by rfl) a
  have h0 : Entails.eval a c4485 := h 4484 (by decide)
  have h1 : Entails.eval a c3813 := h 3812 (by decide)
  have h2 : Entails.eval a c4244 := h 4243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5921 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨40, by decide⟩, false), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5921 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5885, some c5068, some c4081, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5921 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5921 : lratChecker f5921 p5921 = .success := by decide +kernel
theorem unsat5921 : Unsatisfiable (PosFin 65) f5921 := by
  apply lratCheckerSound f5921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5921
  · intro a ha; simp [p5921] at ha; subst a; trivial
  · exact checked5921
theorem derived5921 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5921 := by
  apply localUnsat_implies_entails f5921 [c5885, c5068, c4081] c5921 unsat5921 (by rfl) a
  have h0 : Entails.eval a c5885 := derived5885 a h
  have h1 : Entails.eval a c5068 := h 5067 (by decide)
  have h2 : Entails.eval a c4081 := h 4080 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5922 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5922 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4993, some c4986, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5922 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5922 : lratChecker f5922 p5922 = .success := by decide +kernel
theorem unsat5922 : Unsatisfiable (PosFin 65) f5922 := by
  apply lratCheckerSound f5922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5922
  · intro a ha; simp [p5922] at ha; subst a; trivial
  · exact checked5922
theorem derived5922 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5922 := by
  apply localUnsat_implies_entails f5922 [c4993, c4986] c5922 unsat5922 (by rfl) a
  have h0 : Entails.eval a c4993 := h 4992 (by decide)
  have h1 : Entails.eval a c4986 := h 4985 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5923 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5923 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5078, some c4488, some c5066, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5923 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5923 : lratChecker f5923 p5923 = .success := by decide +kernel
theorem unsat5923 : Unsatisfiable (PosFin 65) f5923 := by
  apply lratCheckerSound f5923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5923
  · intro a ha; simp [p5923] at ha; subst a; trivial
  · exact checked5923
theorem derived5923 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5923 := by
  apply localUnsat_implies_entails f5923 [c5078, c4488, c5066] c5923 unsat5923 (by rfl) a
  have h0 : Entails.eval a c5078 := h 5077 (by decide)
  have h1 : Entails.eval a c4488 := h 4487 (by decide)
  have h2 : Entails.eval a c5066 := h 5065 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5924 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5924 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5917, some c5921, some c5922, some c5923, some c4091, some c4089, some c4080, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5924 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked5924 : lratChecker f5924 p5924 = .success := by decide +kernel
theorem unsat5924 : Unsatisfiable (PosFin 65) f5924 := by
  apply lratCheckerSound f5924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5924
  · intro a ha; simp [p5924] at ha; subst a; trivial
  · exact checked5924
theorem derived5924 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5924 := by
  apply localUnsat_implies_entails f5924 [c5917, c5921, c5922, c5923, c4091, c4089, c4080] c5924 unsat5924 (by rfl) a
  have h0 : Entails.eval a c5917 := derived5917 a h
  have h1 : Entails.eval a c5921 := derived5921 a h
  have h2 : Entails.eval a c5922 := derived5922 a h
  have h3 : Entails.eval a c5923 := derived5923 a h
  have h4 : Entails.eval a c4091 := h 4090 (by decide)
  have h5 : Entails.eval a c4089 := h 4088 (by decide)
  have h6 : Entails.eval a c4080 := h 4079 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5925 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨57, by decide⟩, true), (⟨43, by decide⟩, true), (⟨52, by decide⟩, true), (⟨34, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5925 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4089, some c4080, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p5925 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5925 : lratChecker f5925 p5925 = .success := by decide +kernel
theorem unsat5925 : Unsatisfiable (PosFin 65) f5925 := by
  apply lratCheckerSound f5925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5925
  · intro a ha; simp [p5925] at ha; subst a; trivial
  · exact checked5925
theorem derived5925 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5925 := by
  apply localUnsat_implies_entails f5925 [c4089, c4080] c5925 unsat5925 (by rfl) a
  have h0 : Entails.eval a c4089 := h 4088 (by decide)
  have h1 : Entails.eval a c4080 := h 4079 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5926 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨38, by decide⟩, false), (⟨57, by decide⟩, true), (⟨43, by decide⟩, true), (⟨52, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f5926 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4241, some c4264, some c5386, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p5926 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5926 : lratChecker f5926 p5926 = .success := by decide +kernel
theorem unsat5926 : Unsatisfiable (PosFin 65) f5926 := by
  apply lratCheckerSound f5926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5926
  · intro a ha; simp [p5926] at ha; subst a; trivial
  · exact checked5926
theorem derived5926 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5926 := by
  apply localUnsat_implies_entails f5926 [c4241, c4264, c5386] c5926 unsat5926 (by rfl) a
  have h0 : Entails.eval a c4241 := h 4240 (by decide)
  have h1 : Entails.eval a c4264 := h 4263 (by decide)
  have h2 : Entails.eval a c5386 := h 5385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5927 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨43, by decide⟩, true), (⟨61, by decide⟩, false), (⟨52, by decide⟩, true), (⟨34, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5927 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5925, some c5926, some c4275, some c4250, some c5392, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p5927 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5927 : lratChecker f5927 p5927 = .success := by decide +kernel
theorem unsat5927 : Unsatisfiable (PosFin 65) f5927 := by
  apply lratCheckerSound f5927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5927
  · intro a ha; simp [p5927] at ha; subst a; trivial
  · exact checked5927
theorem derived5927 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5927 := by
  apply localUnsat_implies_entails f5927 [c5925, c5926, c4275, c4250, c5392] c5927 unsat5927 (by rfl) a
  have h0 : Entails.eval a c5925 := derived5925 a h
  have h1 : Entails.eval a c5926 := derived5926 a h
  have h2 : Entails.eval a c4275 := h 4274 (by decide)
  have h3 : Entails.eval a c4250 := h 4249 (by decide)
  have h4 : Entails.eval a c5392 := h 5391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5928 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5928 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5927, some c4251, some c4203, some c4593, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5928 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5928 : lratChecker f5928 p5928 = .success := by decide +kernel
theorem unsat5928 : Unsatisfiable (PosFin 65) f5928 := by
  apply lratCheckerSound f5928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5928
  · intro a ha; simp [p5928] at ha; subst a; trivial
  · exact checked5928
theorem derived5928 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5928 := by
  apply localUnsat_implies_entails f5928 [c5927, c4251, c4203, c4593] c5928 unsat5928 (by rfl) a
  have h0 : Entails.eval a c5927 := derived5927 a h
  have h1 : Entails.eval a c4251 := h 4250 (by decide)
  have h2 : Entails.eval a c4203 := h 4202 (by decide)
  have h3 : Entails.eval a c4593 := h 4592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5929 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨43, by decide⟩, false), (⟨40, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5929 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5198, some c4203, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5929 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5929 : lratChecker f5929 p5929 = .success := by decide +kernel
theorem unsat5929 : Unsatisfiable (PosFin 65) f5929 := by
  apply lratCheckerSound f5929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5929
  · intro a ha; simp [p5929] at ha; subst a; trivial
  · exact checked5929
theorem derived5929 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5929 := by
  apply localUnsat_implies_entails f5929 [c5198, c4203] c5929 unsat5929 (by rfl) a
  have h0 : Entails.eval a c5198 := h 5197 (by decide)
  have h1 : Entails.eval a c4203 := h 4202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5930 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5930 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4189, some c4191, some c4197, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p5930 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5930 : lratChecker f5930 p5930 = .success := by decide +kernel
theorem unsat5930 : Unsatisfiable (PosFin 65) f5930 := by
  apply lratCheckerSound f5930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5930
  · intro a ha; simp [p5930] at ha; subst a; trivial
  · exact checked5930
theorem derived5930 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5930 := by
  apply localUnsat_implies_entails f5930 [c4189, c4191, c4197] c5930 unsat5930 (by rfl) a
  have h0 : Entails.eval a c4189 := h 4188 (by decide)
  have h1 : Entails.eval a c4191 := h 4190 (by decide)
  have h2 : Entails.eval a c4197 := h 4196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5931 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5931 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5928, some c5929, some c5930, some c5189, some c5196, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5931 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5931 : lratChecker f5931 p5931 = .success := by decide +kernel
theorem unsat5931 : Unsatisfiable (PosFin 65) f5931 := by
  apply lratCheckerSound f5931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5931
  · intro a ha; simp [p5931] at ha; subst a; trivial
  · exact checked5931
theorem derived5931 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5931 := by
  apply localUnsat_implies_entails f5931 [c5928, c5929, c5930, c5189, c5196] c5931 unsat5931 (by rfl) a
  have h0 : Entails.eval a c5928 := derived5928 a h
  have h1 : Entails.eval a c5929 := derived5929 a h
  have h2 : Entails.eval a c5930 := derived5930 a h
  have h3 : Entails.eval a c5189 := h 5188 (by decide)
  have h4 : Entails.eval a c5196 := h 5195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5932 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5932 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5931, some c4192, some c4164, some c4584, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p5932 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5932 : lratChecker f5932 p5932 = .success := by decide +kernel
theorem unsat5932 : Unsatisfiable (PosFin 65) f5932 := by
  apply lratCheckerSound f5932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5932
  · intro a ha; simp [p5932] at ha; subst a; trivial
  · exact checked5932
theorem derived5932 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5932 := by
  apply localUnsat_implies_entails f5932 [c5931, c4192, c4164, c4584] c5932 unsat5932 (by rfl) a
  have h0 : Entails.eval a c5931 := derived5931 a h
  have h1 : Entails.eval a c4192 := h 4191 (by decide)
  have h2 : Entails.eval a c4164 := h 4163 (by decide)
  have h3 : Entails.eval a c4584 := h 4583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5933 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5933 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5917, some c5924, some c5932, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5933 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5933 : lratChecker f5933 p5933 = .success := by decide +kernel
theorem unsat5933 : Unsatisfiable (PosFin 65) f5933 := by
  apply lratCheckerSound f5933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5933
  · intro a ha; simp [p5933] at ha; subst a; trivial
  · exact checked5933
theorem derived5933 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5933 := by
  apply localUnsat_implies_entails f5933 [c5917, c5924, c5932] c5933 unsat5933 (by rfl) a
  have h0 : Entails.eval a c5917 := derived5917 a h
  have h1 : Entails.eval a c5924 := derived5924 a h
  have h2 : Entails.eval a c5932 := derived5932 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5934 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5934 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4192, some c5191, some c5245, some c5038, some c5519, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5934 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5934 : lratChecker f5934 p5934 = .success := by decide +kernel
theorem unsat5934 : Unsatisfiable (PosFin 65) f5934 := by
  apply lratCheckerSound f5934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5934
  · intro a ha; simp [p5934] at ha; subst a; trivial
  · exact checked5934
theorem derived5934 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5934 := by
  apply localUnsat_implies_entails f5934 [c4192, c5191, c5245, c5038, c5519] c5934 unsat5934 (by rfl) a
  have h0 : Entails.eval a c4192 := h 4191 (by decide)
  have h1 : Entails.eval a c5191 := h 5190 (by decide)
  have h2 : Entails.eval a c5245 := h 5244 (by decide)
  have h3 : Entails.eval a c5038 := h 5037 (by decide)
  have h4 : Entails.eval a c5519 := h 5518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5935 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨35, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5935 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5927, some c4091, some c4251, some c5900, some c5046, some c5369, some c4446, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5935 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked5935 : lratChecker f5935 p5935 = .success := by decide +kernel
theorem unsat5935 : Unsatisfiable (PosFin 65) f5935 := by
  apply lratCheckerSound f5935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5935
  · intro a ha; simp [p5935] at ha; subst a; trivial
  · exact checked5935
theorem derived5935 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5935 := by
  apply localUnsat_implies_entails f5935 [c5927, c4091, c4251, c5900, c5046, c5369, c4446] c5935 unsat5935 (by rfl) a
  have h0 : Entails.eval a c5927 := derived5927 a h
  have h1 : Entails.eval a c4091 := h 4090 (by decide)
  have h2 : Entails.eval a c4251 := h 4250 (by decide)
  have h3 : Entails.eval a c5900 := derived5900 a h
  have h4 : Entails.eval a c5046 := h 5045 (by decide)
  have h5 : Entails.eval a c5369 := h 5368 (by decide)
  have h6 : Entails.eval a c4446 := h 4445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5936 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5936 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5934, some c5930, some c5935, some c5929, some c5189, some c5196, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5936 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked5936 : lratChecker f5936 p5936 = .success := by decide +kernel
theorem unsat5936 : Unsatisfiable (PosFin 65) f5936 := by
  apply lratCheckerSound f5936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5936
  · intro a ha; simp [p5936] at ha; subst a; trivial
  · exact checked5936
theorem derived5936 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5936 := by
  apply localUnsat_implies_entails f5936 [c5934, c5930, c5935, c5929, c5189, c5196] c5936 unsat5936 (by rfl) a
  have h0 : Entails.eval a c5934 := derived5934 a h
  have h1 : Entails.eval a c5930 := derived5930 a h
  have h2 : Entails.eval a c5935 := derived5935 a h
  have h3 : Entails.eval a c5929 := derived5929 a h
  have h4 : Entails.eval a c5189 := h 5188 (by decide)
  have h5 : Entails.eval a c5196 := h 5195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5937 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5937 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5917, some c5933, some c5936, some c5921, some c5922, some c3955, some c3956, some c3962, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5937 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked5937 : lratChecker f5937 p5937 = .success := by decide +kernel
theorem unsat5937 : Unsatisfiable (PosFin 65) f5937 := by
  apply lratCheckerSound f5937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5937
  · intro a ha; simp [p5937] at ha; subst a; trivial
  · exact checked5937
theorem derived5937 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5937 := by
  apply localUnsat_implies_entails f5937 [c5917, c5933, c5936, c5921, c5922, c3955, c3956, c3962] c5937 unsat5937 (by rfl) a
  have h0 : Entails.eval a c5917 := derived5917 a h
  have h1 : Entails.eval a c5933 := derived5933 a h
  have h2 : Entails.eval a c5936 := derived5936 a h
  have h3 : Entails.eval a c5921 := derived5921 a h
  have h4 : Entails.eval a c5922 := derived5922 a h
  have h5 : Entails.eval a c3955 := h 3954 (by decide)
  have h6 : Entails.eval a c3956 := h 3955 (by decide)
  have h7 : Entails.eval a c3962 := h 3961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5938 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨38, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f5938 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4431, some c5093, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p5938 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5938 : lratChecker f5938 p5938 = .success := by decide +kernel
theorem unsat5938 : Unsatisfiable (PosFin 65) f5938 := by
  apply lratCheckerSound f5938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5938
  · intro a ha; simp [p5938] at ha; subst a; trivial
  · exact checked5938
theorem derived5938 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5938 := by
  apply localUnsat_implies_entails f5938 [c4431, c5093] c5938 unsat5938 (by rfl) a
  have h0 : Entails.eval a c4431 := h 4430 (by decide)
  have h1 : Entails.eval a c5093 := h 5092 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5939 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5939 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5922, some c5938, some c4436, some c5103, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5939 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5939 : lratChecker f5939 p5939 = .success := by decide +kernel
theorem unsat5939 : Unsatisfiable (PosFin 65) f5939 := by
  apply lratCheckerSound f5939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5939
  · intro a ha; simp [p5939] at ha; subst a; trivial
  · exact checked5939
theorem derived5939 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5939 := by
  apply localUnsat_implies_entails f5939 [c5922, c5938, c4436, c5103] c5939 unsat5939 (by rfl) a
  have h0 : Entails.eval a c5922 := derived5922 a h
  have h1 : Entails.eval a c5938 := derived5938 a h
  have h2 : Entails.eval a c4436 := h 4435 (by decide)
  have h3 : Entails.eval a c5103 := h 5102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5940 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨43, by decide⟩, true), (⟨35, by decide⟩, false), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5940 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5103, some c4723, some c3523, some c3652, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5940 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5940 : lratChecker f5940 p5940 = .success := by decide +kernel
theorem unsat5940 : Unsatisfiable (PosFin 65) f5940 := by
  apply lratCheckerSound f5940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5940
  · intro a ha; simp [p5940] at ha; subst a; trivial
  · exact checked5940
theorem derived5940 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5940 := by
  apply localUnsat_implies_entails f5940 [c5103, c4723, c3523, c3652] c5940 unsat5940 (by rfl) a
  have h0 : Entails.eval a c5103 := h 5102 (by decide)
  have h1 : Entails.eval a c4723 := h 4722 (by decide)
  have h2 : Entails.eval a c3523 := h 3522 (by decide)
  have h3 : Entails.eval a c3652 := h 3651 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5941 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5941 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5937, some c5917, some c5922, some c5939, some c5923, some c5940, some c5093, some c5411, some c3643, some c3476, some c5357, some c4725, some c4376, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5941 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked5941 : lratChecker f5941 p5941 = .success := by decide +kernel
theorem unsat5941 : Unsatisfiable (PosFin 65) f5941 := by
  apply lratCheckerSound f5941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5941
  · intro a ha; simp [p5941] at ha; subst a; trivial
  · exact checked5941
theorem derived5941 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5941 := by
  apply localUnsat_implies_entails f5941 [c5937, c5917, c5922, c5939, c5923, c5940, c5093, c5411, c3643, c3476, c5357, c4725, c4376] c5941 unsat5941 (by rfl) a
  have h0 : Entails.eval a c5937 := derived5937 a h
  have h1 : Entails.eval a c5917 := derived5917 a h
  have h2 : Entails.eval a c5922 := derived5922 a h
  have h3 : Entails.eval a c5939 := derived5939 a h
  have h4 : Entails.eval a c5923 := derived5923 a h
  have h5 : Entails.eval a c5940 := derived5940 a h
  have h6 : Entails.eval a c5093 := h 5092 (by decide)
  have h7 : Entails.eval a c5411 := h 5410 (by decide)
  have h8 : Entails.eval a c3643 := h 3642 (by decide)
  have h9 : Entails.eval a c3476 := h 3475 (by decide)
  have h10 : Entails.eval a c5357 := h 5356 (by decide)
  have h11 : Entails.eval a c4725 := h 4724 (by decide)
  have h12 : Entails.eval a c4376 := h 4375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5942 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨64, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5942 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5941, some c5885, some c5068, some c5095, some c5414, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5942 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5942 : lratChecker f5942 p5942 = .success := by decide +kernel
theorem unsat5942 : Unsatisfiable (PosFin 65) f5942 := by
  apply lratCheckerSound f5942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5942
  · intro a ha; simp [p5942] at ha; subst a; trivial
  · exact checked5942
theorem derived5942 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5942 := by
  apply localUnsat_implies_entails f5942 [c5941, c5885, c5068, c5095, c5414] c5942 unsat5942 (by rfl) a
  have h0 : Entails.eval a c5941 := derived5941 a h
  have h1 : Entails.eval a c5885 := derived5885 a h
  have h2 : Entails.eval a c5068 := h 5067 (by decide)
  have h3 : Entails.eval a c5095 := h 5094 (by decide)
  have h4 : Entails.eval a c5414 := h 5413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5943 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5943 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5414, some c4433, some c3646, some c3566, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5943 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5943 : lratChecker f5943 p5943 = .success := by decide +kernel
theorem unsat5943 : Unsatisfiable (PosFin 65) f5943 := by
  apply lratCheckerSound f5943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5943
  · intro a ha; simp [p5943] at ha; subst a; trivial
  · exact checked5943
theorem derived5943 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5943 := by
  apply localUnsat_implies_entails f5943 [c5414, c4433, c3646, c3566] c5943 unsat5943 (by rfl) a
  have h0 : Entails.eval a c5414 := h 5413 (by decide)
  have h1 : Entails.eval a c4433 := h 4432 (by decide)
  have h2 : Entails.eval a c3646 := h 3645 (by decide)
  have h3 : Entails.eval a c3566 := h 3565 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5944 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨52, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5944 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5943, some c4219, some c5245, some c5351, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5944 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5944 : lratChecker f5944 p5944 = .success := by decide +kernel
theorem unsat5944 : Unsatisfiable (PosFin 65) f5944 := by
  apply lratCheckerSound f5944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5944
  · intro a ha; simp [p5944] at ha; subst a; trivial
  · exact checked5944
theorem derived5944 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5944 := by
  apply localUnsat_implies_entails f5944 [c5943, c4219, c5245, c5351] c5944 unsat5944 (by rfl) a
  have h0 : Entails.eval a c5943 := derived5943 a h
  have h1 : Entails.eval a c4219 := h 4218 (by decide)
  have h2 : Entails.eval a c5245 := h 5244 (by decide)
  have h3 : Entails.eval a c5351 := h 5350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5945 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5945 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5944, some c4965, some c3689, some c3465, some c3488, some c5613, some c5563, some c5450, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5945 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked5945 : lratChecker f5945 p5945 = .success := by decide +kernel
theorem unsat5945 : Unsatisfiable (PosFin 65) f5945 := by
  apply lratCheckerSound f5945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5945
  · intro a ha; simp [p5945] at ha; subst a; trivial
  · exact checked5945
theorem derived5945 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5945 := by
  apply localUnsat_implies_entails f5945 [c5944, c4965, c3689, c3465, c3488, c5613, c5563, c5450] c5945 unsat5945 (by rfl) a
  have h0 : Entails.eval a c5944 := derived5944 a h
  have h1 : Entails.eval a c4965 := h 4964 (by decide)
  have h2 : Entails.eval a c3689 := h 3688 (by decide)
  have h3 : Entails.eval a c3465 := h 3464 (by decide)
  have h4 : Entails.eval a c3488 := h 3487 (by decide)
  have h5 : Entails.eval a c5613 := h 5612 (by decide)
  have h6 : Entails.eval a c5563 := h 5562 (by decide)
  have h7 : Entails.eval a c5450 := h 5449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5946 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5946 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5456, some c5446, some c5449, some c5448, some c5453, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p5946 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5946 : lratChecker f5946 p5946 = .success := by decide +kernel
theorem unsat5946 : Unsatisfiable (PosFin 65) f5946 := by
  apply lratCheckerSound f5946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5946
  · intro a ha; simp [p5946] at ha; subst a; trivial
  · exact checked5946
theorem derived5946 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5946 := by
  apply localUnsat_implies_entails f5946 [c5456, c5446, c5449, c5448, c5453] c5946 unsat5946 (by rfl) a
  have h0 : Entails.eval a c5456 := h 5455 (by decide)
  have h1 : Entails.eval a c5446 := h 5445 (by decide)
  have h2 : Entails.eval a c5449 := h 5448 (by decide)
  have h3 : Entails.eval a c5448 := h 5447 (by decide)
  have h4 : Entails.eval a c5453 := h 5452 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5947 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5947 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5610, some c5612, some c5616, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p5947 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5947 : lratChecker f5947 p5947 = .success := by decide +kernel
theorem unsat5947 : Unsatisfiable (PosFin 65) f5947 := by
  apply lratCheckerSound f5947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5947
  · intro a ha; simp [p5947] at ha; subst a; trivial
  · exact checked5947
theorem derived5947 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5947 := by
  apply localUnsat_implies_entails f5947 [c5610, c5612, c5616] c5947 unsat5947 (by rfl) a
  have h0 : Entails.eval a c5610 := h 5609 (by decide)
  have h1 : Entails.eval a c5612 := h 5611 (by decide)
  have h2 : Entails.eval a c5616 := h 5615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5948 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨46, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5948 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5560, some c5562, some c3437, some c4802, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p5948 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5948 : lratChecker f5948 p5948 = .success := by decide +kernel
theorem unsat5948 : Unsatisfiable (PosFin 65) f5948 := by
  apply lratCheckerSound f5948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5948
  · intro a ha; simp [p5948] at ha; subst a; trivial
  · exact checked5948
theorem derived5948 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5948 := by
  apply localUnsat_implies_entails f5948 [c5560, c5562, c3437, c4802] c5948 unsat5948 (by rfl) a
  have h0 : Entails.eval a c5560 := h 5559 (by decide)
  have h1 : Entails.eval a c5562 := h 5561 (by decide)
  have h2 : Entails.eval a c3437 := h 3436 (by decide)
  have h3 : Entails.eval a c4802 := h 4801 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5949 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨47, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5949 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5430, some c4307, some c3498, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5949 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5949 : lratChecker f5949 p5949 = .success := by decide +kernel
theorem unsat5949 : Unsatisfiable (PosFin 65) f5949 := by
  apply lratCheckerSound f5949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5949
  · intro a ha; simp [p5949] at ha; subst a; trivial
  · exact checked5949
theorem derived5949 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5949 := by
  apply localUnsat_implies_entails f5949 [c5430, c4307, c3498] c5949 unsat5949 (by rfl) a
  have h0 : Entails.eval a c5430 := h 5429 (by decide)
  have h1 : Entails.eval a c4307 := h 4306 (by decide)
  have h2 : Entails.eval a c3498 := h 3497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5950 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5950 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4972, some c4970, some c4962, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5950 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5950 : lratChecker f5950 p5950 = .success := by decide +kernel
theorem unsat5950 : Unsatisfiable (PosFin 65) f5950 := by
  apply lratCheckerSound f5950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5950
  · intro a ha; simp [p5950] at ha; subst a; trivial
  · exact checked5950
theorem derived5950 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5950 := by
  apply localUnsat_implies_entails f5950 [c4972, c4970, c4962] c5950 unsat5950 (by rfl) a
  have h0 : Entails.eval a c4972 := h 4971 (by decide)
  have h1 : Entails.eval a c4970 := h 4969 (by decide)
  have h2 : Entails.eval a c4962 := h 4961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5951 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨46, by decide⟩, true), (⟨41, by decide⟩, true), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5951 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5947, some c5949, some c5948, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5951 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5951 : lratChecker f5951 p5951 = .success := by decide +kernel
theorem unsat5951 : Unsatisfiable (PosFin 65) f5951 := by
  apply lratCheckerSound f5951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5951
  · intro a ha; simp [p5951] at ha; subst a; trivial
  · exact checked5951
theorem derived5951 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5951 := by
  apply localUnsat_implies_entails f5951 [c5947, c5949, c5948] c5951 unsat5951 (by rfl) a
  have h0 : Entails.eval a c5947 := derived5947 a h
  have h1 : Entails.eval a c5949 := derived5949 a h
  have h2 : Entails.eval a c5948 := derived5948 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5952 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5952 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5947, some c5946, some c5951, some c3698, some c3686, some c3688, some c3725, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5952 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked5952 : lratChecker f5952 p5952 = .success := by decide +kernel
theorem unsat5952 : Unsatisfiable (PosFin 65) f5952 := by
  apply lratCheckerSound f5952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5952
  · intro a ha; simp [p5952] at ha; subst a; trivial
  · exact checked5952
theorem derived5952 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5952 := by
  apply localUnsat_implies_entails f5952 [c5947, c5946, c5951, c3698, c3686, c3688, c3725] c5952 unsat5952 (by rfl) a
  have h0 : Entails.eval a c5947 := derived5947 a h
  have h1 : Entails.eval a c5946 := derived5946 a h
  have h2 : Entails.eval a c5951 := derived5951 a h
  have h3 : Entails.eval a c3698 := h 3697 (by decide)
  have h4 : Entails.eval a c3686 := h 3685 (by decide)
  have h5 : Entails.eval a c3688 := h 3687 (by decide)
  have h6 : Entails.eval a c3725 := h 3724 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5953 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5953 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3462, some c3464, some c3473, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5953 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5953 : lratChecker f5953 p5953 = .success := by decide +kernel
theorem unsat5953 : Unsatisfiable (PosFin 65) f5953 := by
  apply lratCheckerSound f5953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5953
  · intro a ha; simp [p5953] at ha; subst a; trivial
  · exact checked5953
theorem derived5953 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5953 := by
  apply localUnsat_implies_entails f5953 [c3462, c3464, c3473] c5953 unsat5953 (by rfl) a
  have h0 : Entails.eval a c3462 := h 3461 (by decide)
  have h1 : Entails.eval a c3464 := h 3463 (by decide)
  have h2 : Entails.eval a c3473 := h 3472 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5954 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5954 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5937, some c5942, some c5945, some c5917, some c5950, some c5952, some c5953, some c3698, some c3686, some c3696, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5954 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked5954 : lratChecker f5954 p5954 = .success := by decide +kernel
theorem unsat5954 : Unsatisfiable (PosFin 65) f5954 := by
  apply lratCheckerSound f5954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5954
  · intro a ha; simp [p5954] at ha; subst a; trivial
  · exact checked5954
theorem derived5954 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5954 := by
  apply localUnsat_implies_entails f5954 [c5937, c5942, c5945, c5917, c5950, c5952, c5953, c3698, c3686, c3696] c5954 unsat5954 (by rfl) a
  have h0 : Entails.eval a c5937 := derived5937 a h
  have h1 : Entails.eval a c5942 := derived5942 a h
  have h2 : Entails.eval a c5945 := derived5945 a h
  have h3 : Entails.eval a c5917 := derived5917 a h
  have h4 : Entails.eval a c5950 := derived5950 a h
  have h5 : Entails.eval a c5952 := derived5952 a h
  have h6 : Entails.eval a c5953 := derived5953 a h
  have h7 : Entails.eval a c3698 := h 3697 (by decide)
  have h8 : Entails.eval a c3686 := h 3685 (by decide)
  have h9 : Entails.eval a c3696 := h 3695 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5955 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨33, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5955 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3698, some c3686, some c3696, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5955 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5955 : lratChecker f5955 p5955 = .success := by decide +kernel
theorem unsat5955 : Unsatisfiable (PosFin 65) f5955 := by
  apply lratCheckerSound f5955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5955
  · intro a ha; simp [p5955] at ha; subst a; trivial
  · exact checked5955
theorem derived5955 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5955 := by
  apply localUnsat_implies_entails f5955 [c3698, c3686, c3696] c5955 unsat5955 (by rfl) a
  have h0 : Entails.eval a c3698 := h 3697 (by decide)
  have h1 : Entails.eval a c3686 := h 3685 (by decide)
  have h2 : Entails.eval a c3696 := h 3695 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5956 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨39, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5956 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3789, some c5042, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5956 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5956 : lratChecker f5956 p5956 = .success := by decide +kernel
theorem unsat5956 : Unsatisfiable (PosFin 65) f5956 := by
  apply lratCheckerSound f5956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5956
  · intro a ha; simp [p5956] at ha; subst a; trivial
  · exact checked5956
theorem derived5956 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5956 := by
  apply localUnsat_implies_entails f5956 [c3789, c5042] c5956 unsat5956 (by rfl) a
  have h0 : Entails.eval a c3789 := h 3788 (by decide)
  have h1 : Entails.eval a c5042 := h 5041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5957 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5957 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3776, some c5035, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p5957 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5957 : lratChecker f5957 p5957 = .success := by decide +kernel
theorem unsat5957 : Unsatisfiable (PosFin 65) f5957 := by
  apply lratCheckerSound f5957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5957
  · intro a ha; simp [p5957] at ha; subst a; trivial
  · exact checked5957
theorem derived5957 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5957 := by
  apply localUnsat_implies_entails f5957 [c3776, c5035] c5957 unsat5957 (by rfl) a
  have h0 : Entails.eval a c3776 := h 3775 (by decide)
  have h1 : Entails.eval a c5035 := h 5034 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5958 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5958 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5955, some c5956, some c5036, some c5007, some c5633, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5958 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5958 : lratChecker f5958 p5958 = .success := by decide +kernel
theorem unsat5958 : Unsatisfiable (PosFin 65) f5958 := by
  apply lratCheckerSound f5958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5958
  · intro a ha; simp [p5958] at ha; subst a; trivial
  · exact checked5958
theorem derived5958 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5958 := by
  apply localUnsat_implies_entails f5958 [c5955, c5956, c5036, c5007, c5633] c5958 unsat5958 (by rfl) a
  have h0 : Entails.eval a c5955 := derived5955 a h
  have h1 : Entails.eval a c5956 := derived5956 a h
  have h2 : Entails.eval a c5036 := h 5035 (by decide)
  have h3 : Entails.eval a c5007 := h 5006 (by decide)
  have h4 : Entails.eval a c5633 := h 5632 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5959 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨52, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5959 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4140, some c4148, some c4147, some c4138, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5959 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5959 : lratChecker f5959 p5959 = .success := by decide +kernel
theorem unsat5959 : Unsatisfiable (PosFin 65) f5959 := by
  apply lratCheckerSound f5959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5959
  · intro a ha; simp [p5959] at ha; subst a; trivial
  · exact checked5959
theorem derived5959 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5959 := by
  apply localUnsat_implies_entails f5959 [c4140, c4148, c4147, c4138] c5959 unsat5959 (by rfl) a
  have h0 : Entails.eval a c4140 := h 4139 (by decide)
  have h1 : Entails.eval a c4148 := h 4147 (by decide)
  have h2 : Entails.eval a c4147 := h 4146 (by decide)
  have h3 : Entails.eval a c4138 := h 4137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5960 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨58, by decide⟩, false), (⟨57, by decide⟩, true), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨41, by decide⟩, true), (⟨33, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f5960 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4306, some c5561, some c4445, some c4560, some c3565, some c5788, some c5241, some c5633, some c5634, some c5748, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p5960 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked5960 : lratChecker f5960 p5960 = .success := by decide +kernel
theorem unsat5960 : Unsatisfiable (PosFin 65) f5960 := by
  apply lratCheckerSound f5960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5960
  · intro a ha; simp [p5960] at ha; subst a; trivial
  · exact checked5960
theorem derived5960 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5960 := by
  apply localUnsat_implies_entails f5960 [c4306, c5561, c4445, c4560, c3565, c5788, c5241, c5633, c5634, c5748] c5960 unsat5960 (by rfl) a
  have h0 : Entails.eval a c4306 := h 4305 (by decide)
  have h1 : Entails.eval a c5561 := h 5560 (by decide)
  have h2 : Entails.eval a c4445 := h 4444 (by decide)
  have h3 : Entails.eval a c4560 := h 4559 (by decide)
  have h4 : Entails.eval a c3565 := h 3564 (by decide)
  have h5 : Entails.eval a c5788 := h 5787 (by decide)
  have h6 : Entails.eval a c5241 := h 5240 (by decide)
  have h7 : Entails.eval a c5633 := h 5632 (by decide)
  have h8 : Entails.eval a c5634 := h 5633 (by decide)
  have h9 : Entails.eval a c5748 := h 5747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5961 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨47, by decide⟩, false), (⟨41, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5961 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5357, some c5196, some c4725, some c4010, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p5961 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5961 : lratChecker f5961 p5961 = .success := by decide +kernel
theorem unsat5961 : Unsatisfiable (PosFin 65) f5961 := by
  apply lratCheckerSound f5961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5961
  · intro a ha; simp [p5961] at ha; subst a; trivial
  · exact checked5961
theorem derived5961 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5961 := by
  apply localUnsat_implies_entails f5961 [c5357, c5196, c4725, c4010] c5961 unsat5961 (by rfl) a
  have h0 : Entails.eval a c5357 := h 5356 (by decide)
  have h1 : Entails.eval a c5196 := h 5195 (by decide)
  have h2 : Entails.eval a c4725 := h 4724 (by decide)
  have h3 : Entails.eval a c4010 := h 4009 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5962 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨41, by decide⟩, true), (⟨33, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5962 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5960, some c5636, some c5190, some c5517, some c5241, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p5962 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5962 : lratChecker f5962 p5962 = .success := by decide +kernel
theorem unsat5962 : Unsatisfiable (PosFin 65) f5962 := by
  apply lratCheckerSound f5962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5962
  · intro a ha; simp [p5962] at ha; subst a; trivial
  · exact checked5962
theorem derived5962 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5962 := by
  apply localUnsat_implies_entails f5962 [c5960, c5636, c5190, c5517, c5241] c5962 unsat5962 (by rfl) a
  have h0 : Entails.eval a c5960 := derived5960 a h
  have h1 : Entails.eval a c5636 := h 5635 (by decide)
  have h2 : Entails.eval a c5190 := h 5189 (by decide)
  have h3 : Entails.eval a c5517 := h 5516 (by decide)
  have h4 : Entails.eval a c5241 := h 5240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5963 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5963 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5917, some c5937, some c5942, some c5945, some c5954, some c5958, some c5953, some c5947, some c5959, some c5961, some c5962, some c4746, some c3450, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5963 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked5963 : lratChecker f5963 p5963 = .success := by decide +kernel
theorem unsat5963 : Unsatisfiable (PosFin 65) f5963 := by
  apply lratCheckerSound f5963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5963
  · intro a ha; simp [p5963] at ha; subst a; trivial
  · exact checked5963
theorem derived5963 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5963 := by
  apply localUnsat_implies_entails f5963 [c5917, c5937, c5942, c5945, c5954, c5958, c5953, c5947, c5959, c5961, c5962, c4746, c3450] c5963 unsat5963 (by rfl) a
  have h0 : Entails.eval a c5917 := derived5917 a h
  have h1 : Entails.eval a c5937 := derived5937 a h
  have h2 : Entails.eval a c5942 := derived5942 a h
  have h3 : Entails.eval a c5945 := derived5945 a h
  have h4 : Entails.eval a c5954 := derived5954 a h
  have h5 : Entails.eval a c5958 := derived5958 a h
  have h6 : Entails.eval a c5953 := derived5953 a h
  have h7 : Entails.eval a c5947 := derived5947 a h
  have h8 : Entails.eval a c5959 := derived5959 a h
  have h9 : Entails.eval a c5961 := derived5961 a h
  have h10 : Entails.eval a c5962 := derived5962 a h
  have h11 : Entails.eval a c4746 := h 4745 (by decide)
  have h12 : Entails.eval a c3450 := h 3449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5964 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5964 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4746, some c3450, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5964 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5964 : lratChecker f5964 p5964 = .success := by decide +kernel
theorem unsat5964 : Unsatisfiable (PosFin 65) f5964 := by
  apply lratCheckerSound f5964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5964
  · intro a ha; simp [p5964] at ha; subst a; trivial
  · exact checked5964
theorem derived5964 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5964 := by
  apply localUnsat_implies_entails f5964 [c4746, c3450] c5964 unsat5964 (by rfl) a
  have h0 : Entails.eval a c4746 := h 4745 (by decide)
  have h1 : Entails.eval a c3450 := h 3449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5965 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨57, by decide⟩, true), (⟨38, by decide⟩, true), (⟨47, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5965 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5953, some c3447, some c3446, some c3439, some c4306, some c5218, some c4417, some c3507, some c4339, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5965 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked5965 : lratChecker f5965 p5965 = .success := by decide +kernel
theorem unsat5965 : Unsatisfiable (PosFin 65) f5965 := by
  apply lratCheckerSound f5965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5965
  · intro a ha; simp [p5965] at ha; subst a; trivial
  · exact checked5965
theorem derived5965 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5965 := by
  apply localUnsat_implies_entails f5965 [c5953, c3447, c3446, c3439, c4306, c5218, c4417, c3507, c4339] c5965 unsat5965 (by rfl) a
  have h0 : Entails.eval a c5953 := derived5953 a h
  have h1 : Entails.eval a c3447 := h 3446 (by decide)
  have h2 : Entails.eval a c3446 := h 3445 (by decide)
  have h3 : Entails.eval a c3439 := h 3438 (by decide)
  have h4 : Entails.eval a c4306 := h 4305 (by decide)
  have h5 : Entails.eval a c5218 := h 5217 (by decide)
  have h6 : Entails.eval a c4417 := h 4416 (by decide)
  have h7 : Entails.eval a c3507 := h 3506 (by decide)
  have h8 : Entails.eval a c4339 := h 4338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5966 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5966 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5955, some c5963, some c5917, some c5953, some c5947, some c5952, some c5964, some c5965, some c4743, some c4694, some c4788, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5966 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked5966 : lratChecker f5966 p5966 = .success := by decide +kernel
theorem unsat5966 : Unsatisfiable (PosFin 65) f5966 := by
  apply lratCheckerSound f5966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5966
  · intro a ha; simp [p5966] at ha; subst a; trivial
  · exact checked5966
theorem derived5966 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5966 := by
  apply localUnsat_implies_entails f5966 [c5955, c5963, c5917, c5953, c5947, c5952, c5964, c5965, c4743, c4694, c4788] c5966 unsat5966 (by rfl) a
  have h0 : Entails.eval a c5955 := derived5955 a h
  have h1 : Entails.eval a c5963 := derived5963 a h
  have h2 : Entails.eval a c5917 := derived5917 a h
  have h3 : Entails.eval a c5953 := derived5953 a h
  have h4 : Entails.eval a c5947 := derived5947 a h
  have h5 : Entails.eval a c5952 := derived5952 a h
  have h6 : Entails.eval a c5964 := derived5964 a h
  have h7 : Entails.eval a c5965 := derived5965 a h
  have h8 : Entails.eval a c4743 := h 4742 (by decide)
  have h9 : Entails.eval a c4694 := h 4693 (by decide)
  have h10 : Entails.eval a c4788 := h 4787 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5967 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨43, by decide⟩, false), (⟨57, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f5967 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3933, some c3563, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p5967 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5967 : lratChecker f5967 p5967 = .success := by decide +kernel
theorem unsat5967 : Unsatisfiable (PosFin 65) f5967 := by
  apply lratCheckerSound f5967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5967
  · intro a ha; simp [p5967] at ha; subst a; trivial
  · exact checked5967
theorem derived5967 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5967 := by
  apply localUnsat_implies_entails f5967 [c3933, c3563] c5967 unsat5967 (by rfl) a
  have h0 : Entails.eval a c3933 := h 3932 (by decide)
  have h1 : Entails.eval a c3563 := h 3562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5968 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨48, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5968 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5927, some c5967, some c3941, some c4616, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5968 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5968 : lratChecker f5968 p5968 = .success := by decide +kernel
theorem unsat5968 : Unsatisfiable (PosFin 65) f5968 := by
  apply lratCheckerSound f5968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5968
  · intro a ha; simp [p5968] at ha; subst a; trivial
  · exact checked5968
theorem derived5968 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5968 := by
  apply localUnsat_implies_entails f5968 [c5927, c5967, c3941, c4616] c5968 unsat5968 (by rfl) a
  have h0 : Entails.eval a c5927 := derived5927 a h
  have h1 : Entails.eval a c5967 := derived5967 a h
  have h2 : Entails.eval a c3941 := h 3940 (by decide)
  have h3 : Entails.eval a c4616 := h 4615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5969 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5969 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5963, some c5917, some c5955, some c5966, some c5930, some c5968, some c3948, some c4746, some c3526, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5969 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked5969 : lratChecker f5969 p5969 = .success := by decide +kernel
theorem unsat5969 : Unsatisfiable (PosFin 65) f5969 := by
  apply lratCheckerSound f5969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5969
  · intro a ha; simp [p5969] at ha; subst a; trivial
  · exact checked5969
theorem derived5969 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5969 := by
  apply localUnsat_implies_entails f5969 [c5963, c5917, c5955, c5966, c5930, c5968, c3948, c4746, c3526] c5969 unsat5969 (by rfl) a
  have h0 : Entails.eval a c5963 := derived5963 a h
  have h1 : Entails.eval a c5917 := derived5917 a h
  have h2 : Entails.eval a c5955 := derived5955 a h
  have h3 : Entails.eval a c5966 := derived5966 a h
  have h4 : Entails.eval a c5930 := derived5930 a h
  have h5 : Entails.eval a c5968 := derived5968 a h
  have h6 : Entails.eval a c3948 := h 3947 (by decide)
  have h7 : Entails.eval a c4746 := h 4745 (by decide)
  have h8 : Entails.eval a c3526 := h 3525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5970 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨48, by decide⟩, false), (⟨34, by decide⟩, true), (⟨39, by decide⟩, false), (⟨37, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5970 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4035, some c5498, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5970 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5970 : lratChecker f5970 p5970 = .success := by decide +kernel
theorem unsat5970 : Unsatisfiable (PosFin 65) f5970 := by
  apply lratCheckerSound f5970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5970
  · intro a ha; simp [p5970] at ha; subst a; trivial
  · exact checked5970
theorem derived5970 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5970 := by
  apply localUnsat_implies_entails f5970 [c4035, c5498] c5970 unsat5970 (by rfl) a
  have h0 : Entails.eval a c4035 := h 4034 (by decide)
  have h1 : Entails.eval a c5498 := h 5497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5971 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨57, by decide⟩, true), (⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5971 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5493, some c5492, some c5497, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p5971 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5971 : lratChecker f5971 p5971 = .success := by decide +kernel
theorem unsat5971 : Unsatisfiable (PosFin 65) f5971 := by
  apply lratCheckerSound f5971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5971
  · intro a ha; simp [p5971] at ha; subst a; trivial
  · exact checked5971
theorem derived5971 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5971 := by
  apply localUnsat_implies_entails f5971 [c5493, c5492, c5497] c5971 unsat5971 (by rfl) a
  have h0 : Entails.eval a c5493 := h 5492 (by decide)
  have h1 : Entails.eval a c5492 := h 5491 (by decide)
  have h2 : Entails.eval a c5497 := h 5496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5972 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5972 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5969, some c5963, some c5917, some c5930, some c5970, some c5971, some c4162, some c4170, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5972 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked5972 : lratChecker f5972 p5972 = .success := by decide +kernel
theorem unsat5972 : Unsatisfiable (PosFin 65) f5972 := by
  apply lratCheckerSound f5972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5972
  · intro a ha; simp [p5972] at ha; subst a; trivial
  · exact checked5972
theorem derived5972 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5972 := by
  apply localUnsat_implies_entails f5972 [c5969, c5963, c5917, c5930, c5970, c5971, c4162, c4170] c5972 unsat5972 (by rfl) a
  have h0 : Entails.eval a c5969 := derived5969 a h
  have h1 : Entails.eval a c5963 := derived5963 a h
  have h2 : Entails.eval a c5917 := derived5917 a h
  have h3 : Entails.eval a c5930 := derived5930 a h
  have h4 : Entails.eval a c5970 := derived5970 a h
  have h5 : Entails.eval a c5971 := derived5971 a h
  have h6 : Entails.eval a c4162 := h 4161 (by decide)
  have h7 : Entails.eval a c4170 := h 4169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5973 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5973 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5917, some c5969, some c5972, some c5959, some c5947, some c4116, some c4117, some c4122, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5973 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked5973 : lratChecker f5973 p5973 = .success := by decide +kernel
theorem unsat5973 : Unsatisfiable (PosFin 65) f5973 := by
  apply lratCheckerSound f5973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5973
  · intro a ha; simp [p5973] at ha; subst a; trivial
  · exact checked5973
theorem derived5973 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5973 := by
  apply localUnsat_implies_entails f5973 [c5917, c5969, c5972, c5959, c5947, c4116, c4117, c4122] c5973 unsat5973 (by rfl) a
  have h0 : Entails.eval a c5917 := derived5917 a h
  have h1 : Entails.eval a c5969 := derived5969 a h
  have h2 : Entails.eval a c5972 := derived5972 a h
  have h3 : Entails.eval a c5959 := derived5959 a h
  have h4 : Entails.eval a c5947 := derived5947 a h
  have h5 : Entails.eval a c4116 := h 4115 (by decide)
  have h6 : Entails.eval a c4117 := h 4116 (by decide)
  have h7 : Entails.eval a c4122 := h 4121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5974 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨54, by decide⟩, false), (⟨47, by decide⟩, true), (⟨40, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5974 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4409, some c3625, some c5889, some c3546, some c5167, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5974 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5974 : lratChecker f5974 p5974 = .success := by decide +kernel
theorem unsat5974 : Unsatisfiable (PosFin 65) f5974 := by
  apply lratCheckerSound f5974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5974
  · intro a ha; simp [p5974] at ha; subst a; trivial
  · exact checked5974
theorem derived5974 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5974 := by
  apply localUnsat_implies_entails f5974 [c4409, c3625, c5889, c3546, c5167] c5974 unsat5974 (by rfl) a
  have h0 : Entails.eval a c4409 := h 4408 (by decide)
  have h1 : Entails.eval a c3625 := h 3624 (by decide)
  have h2 : Entails.eval a c5889 := derived5889 a h
  have h3 : Entails.eval a c3546 := h 3545 (by decide)
  have h4 : Entails.eval a c5167 := h 5166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5975 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨47, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5975 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5974, some c4407, some c3620, some c4501, some c3497, some c5220, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5975 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked5975 : lratChecker f5975 p5975 = .success := by decide +kernel
theorem unsat5975 : Unsatisfiable (PosFin 65) f5975 := by
  apply lratCheckerSound f5975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5975
  · intro a ha; simp [p5975] at ha; subst a; trivial
  · exact checked5975
theorem derived5975 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5975 := by
  apply localUnsat_implies_entails f5975 [c5974, c4407, c3620, c4501, c3497, c5220] c5975 unsat5975 (by rfl) a
  have h0 : Entails.eval a c5974 := derived5974 a h
  have h1 : Entails.eval a c4407 := h 4406 (by decide)
  have h2 : Entails.eval a c3620 := h 3619 (by decide)
  have h3 : Entails.eval a c4501 := h 4500 (by decide)
  have h4 : Entails.eval a c3497 := h 3496 (by decide)
  have h5 : Entails.eval a c5220 := h 5219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5976 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f5976 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4405, some c3615, some c5166, some c3535, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p5976 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5976 : lratChecker f5976 p5976 = .success := by decide +kernel
theorem unsat5976 : Unsatisfiable (PosFin 65) f5976 := by
  apply lratCheckerSound f5976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5976
  · intro a ha; simp [p5976] at ha; subst a; trivial
  · exact checked5976
theorem derived5976 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5976 := by
  apply localUnsat_implies_entails f5976 [c4405, c3615, c5166, c3535] c5976 unsat5976 (by rfl) a
  have h0 : Entails.eval a c4405 := h 4404 (by decide)
  have h1 : Entails.eval a c3615 := h 3614 (by decide)
  have h2 : Entails.eval a c5166 := h 5165 (by decide)
  have h3 : Entails.eval a c3535 := h 3534 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5977 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨34, by decide⟩, false), (⟨63, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5977 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5975, some c5976, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5977 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5977 : lratChecker f5977 p5977 = .success := by decide +kernel
theorem unsat5977 : Unsatisfiable (PosFin 65) f5977 := by
  apply lratCheckerSound f5977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5977
  · intro a ha; simp [p5977] at ha; subst a; trivial
  · exact checked5977
theorem derived5977 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5977 := by
  apply localUnsat_implies_entails f5977 [c5975, c5976] c5977 unsat5977 (by rfl) a
  have h0 : Entails.eval a c5975 := derived5975 a h
  have h1 : Entails.eval a c5976 := derived5976 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5978 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5978 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5959, some c5977, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5978 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5978 : lratChecker f5978 p5978 = .success := by decide +kernel
theorem unsat5978 : Unsatisfiable (PosFin 65) f5978 := by
  apply lratCheckerSound f5978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5978
  · intro a ha; simp [p5978] at ha; subst a; trivial
  · exact checked5978
theorem derived5978 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5978 := by
  apply localUnsat_implies_entails f5978 [c5959, c5977] c5978 unsat5978 (by rfl) a
  have h0 : Entails.eval a c5959 := derived5959 a h
  have h1 : Entails.eval a c5977 := derived5977 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5979 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5979 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4059, some c3941, some c4509, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5979 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5979 : lratChecker f5979 p5979 = .success := by decide +kernel
theorem unsat5979 : Unsatisfiable (PosFin 65) f5979 := by
  apply lratCheckerSound f5979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5979
  · intro a ha; simp [p5979] at ha; subst a; trivial
  · exact checked5979
theorem derived5979 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5979 := by
  apply localUnsat_implies_entails f5979 [c4059, c3941, c4509] c5979 unsat5979 (by rfl) a
  have h0 : Entails.eval a c4059 := h 4058 (by decide)
  have h1 : Entails.eval a c3941 := h 3940 (by decide)
  have h2 : Entails.eval a c4509 := h 4508 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5980 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5980 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5979, some c3934, some c4051, some c4499, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5980 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5980 : lratChecker f5980 p5980 = .success := by decide +kernel
theorem unsat5980 : Unsatisfiable (PosFin 65) f5980 := by
  apply lratCheckerSound f5980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5980
  · intro a ha; simp [p5980] at ha; subst a; trivial
  · exact checked5980
theorem derived5980 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5980 := by
  apply localUnsat_implies_entails f5980 [c5979, c3934, c4051, c4499] c5980 unsat5980 (by rfl) a
  have h0 : Entails.eval a c5979 := derived5979 a h
  have h1 : Entails.eval a c3934 := h 3933 (by decide)
  have h2 : Entails.eval a c4051 := h 4050 (by decide)
  have h3 : Entails.eval a c4499 := h 4498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived5980

end CochromaticTwenty.Certificates.FixedCore1
