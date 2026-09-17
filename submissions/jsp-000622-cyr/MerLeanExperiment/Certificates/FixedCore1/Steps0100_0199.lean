import MerLeanExperiment.Certificates.FixedCore1.Steps0000_0099

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c5981 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨47, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5981 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4304, some c5216, some c4386, some c4512, some c4500, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5981 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked5981 : lratChecker f5981 p5981 = .success := by decide +kernel
theorem unsat5981 : Unsatisfiable (PosFin 65) f5981 := by
  apply lratCheckerSound f5981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5981
  · intro a ha; simp [p5981] at ha; subst a; trivial
  · exact checked5981
theorem derived5981 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5981 := by
  apply localUnsat_implies_entails f5981 [c4304, c5216, c4386, c4512, c4500] c5981 unsat5981 (by rfl) a
  have h0 : Entails.eval a c4304 := h 4303 (by decide)
  have h1 : Entails.eval a c5216 := h 5215 (by decide)
  have h2 : Entails.eval a c4386 := h 4385 (by decide)
  have h3 : Entails.eval a c4512 := h 4511 (by decide)
  have h4 : Entails.eval a c4500 := h 4499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c5982 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨54, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5982 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4488, some c4509, some c5547, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5982 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5982 : lratChecker f5982 p5982 = .success := by decide +kernel
theorem unsat5982 : Unsatisfiable (PosFin 65) f5982 := by
  apply lratCheckerSound f5982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5982
  · intro a ha; simp [p5982] at ha; subst a; trivial
  · exact checked5982
theorem derived5982 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5982 := by
  apply localUnsat_implies_entails f5982 [c4488, c4509, c5547] c5982 unsat5982 (by rfl) a
  have h0 : Entails.eval a c4488 := h 4487 (by decide)
  have h1 : Entails.eval a c4509 := h 4508 (by decide)
  have h2 : Entails.eval a c5547 := h 5546 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5983 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5983 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5963, some c5917, some c5973, some c5980, some c5977, some c5978, some c5981, some c5982, some c4452, some c4470, some c4305, some c4307, some c5701, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5983 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked5983 : lratChecker f5983 p5983 = .success := by decide +kernel
theorem unsat5983 : Unsatisfiable (PosFin 65) f5983 := by
  apply lratCheckerSound f5983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5983
  · intro a ha; simp [p5983] at ha; subst a; trivial
  · exact checked5983
theorem derived5983 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5983 := by
  apply localUnsat_implies_entails f5983 [c5963, c5917, c5973, c5980, c5977, c5978, c5981, c5982, c4452, c4470, c4305, c4307, c5701] c5983 unsat5983 (by rfl) a
  have h0 : Entails.eval a c5963 := derived5963 a h
  have h1 : Entails.eval a c5917 := derived5917 a h
  have h2 : Entails.eval a c5973 := derived5973 a h
  have h3 : Entails.eval a c5980 := derived5980 a h
  have h4 : Entails.eval a c5977 := derived5977 a h
  have h5 : Entails.eval a c5978 := derived5978 a h
  have h6 : Entails.eval a c5981 := derived5981 a h
  have h7 : Entails.eval a c5982 := derived5982 a h
  have h8 : Entails.eval a c4452 := h 4451 (by decide)
  have h9 : Entails.eval a c4470 := h 4469 (by decide)
  have h10 : Entails.eval a c4305 := h 4304 (by decide)
  have h11 : Entails.eval a c4307 := h 4306 (by decide)
  have h12 : Entails.eval a c5701 := h 5700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5984 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5984 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5983, some c5963, some c5885, some c5943, some c5698, some c5717, some c5221, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5984 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked5984 : lratChecker f5984 p5984 = .success := by decide +kernel
theorem unsat5984 : Unsatisfiable (PosFin 65) f5984 := by
  apply lratCheckerSound f5984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5984
  · intro a ha; simp [p5984] at ha; subst a; trivial
  · exact checked5984
theorem derived5984 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5984 := by
  apply localUnsat_implies_entails f5984 [c5983, c5963, c5885, c5943, c5698, c5717, c5221] c5984 unsat5984 (by rfl) a
  have h0 : Entails.eval a c5983 := derived5983 a h
  have h1 : Entails.eval a c5963 := derived5963 a h
  have h2 : Entails.eval a c5885 := derived5885 a h
  have h3 : Entails.eval a c5943 := derived5943 a h
  have h4 : Entails.eval a c5698 := h 5697 (by decide)
  have h5 : Entails.eval a c5717 := h 5716 (by decide)
  have h6 : Entails.eval a c5221 := h 5220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5985 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨45, by decide⟩, false), (⟨39, by decide⟩, true), (⟨46, by decide⟩, false), (⟨40, by decide⟩, true), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5985 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4743, some c4886, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5985 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5985 : lratChecker f5985 p5985 = .success := by decide +kernel
theorem unsat5985 : Unsatisfiable (PosFin 65) f5985 := by
  apply lratCheckerSound f5985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5985
  · intro a ha; simp [p5985] at ha; subst a; trivial
  · exact checked5985
theorem derived5985 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5985 := by
  apply localUnsat_implies_entails f5985 [c4743, c4886] c5985 unsat5985 (by rfl) a
  have h0 : Entails.eval a c4743 := h 4742 (by decide)
  have h1 : Entails.eval a c4886 := h 4885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5986 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨54, by decide⟩, true), (⟨48, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5986 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4364, some c4362, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p5986 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked5986 : lratChecker f5986 p5986 = .success := by decide +kernel
theorem unsat5986 : Unsatisfiable (PosFin 65) f5986 := by
  apply lratCheckerSound f5986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5986
  · intro a ha; simp [p5986] at ha; subst a; trivial
  · exact checked5986
theorem derived5986 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5986 := by
  apply localUnsat_implies_entails f5986 [c4364, c4362] c5986 unsat5986 (by rfl) a
  have h0 : Entails.eval a c4364 := h 4363 (by decide)
  have h1 : Entails.eval a c4362 := h 4361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c5987 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5987 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5984, some c5983, some c5963, some c5917, some c5221, some c4390, some c4561, some c5660, some c4164, some c4141, some c5450, some c3689, some c5943, some c3465, some c5351, some c5985, some c5986, some c4735, some c4669, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5987 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked5987 : lratChecker f5987 p5987 = .success := by decide +kernel
theorem unsat5987 : Unsatisfiable (PosFin 65) f5987 := by
  apply lratCheckerSound f5987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5987
  · intro a ha; simp [p5987] at ha; subst a; trivial
  · exact checked5987
theorem derived5987 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5987 := by
  apply localUnsat_implies_entails f5987 [c5984, c5983, c5963, c5917, c5221, c4390, c4561, c5660, c4164, c4141, c5450, c3689, c5943, c3465, c5351, c5985, c5986, c4735, c4669] c5987 unsat5987 (by rfl) a
  have h0 : Entails.eval a c5984 := derived5984 a h
  have h1 : Entails.eval a c5983 := derived5983 a h
  have h2 : Entails.eval a c5963 := derived5963 a h
  have h3 : Entails.eval a c5917 := derived5917 a h
  have h4 : Entails.eval a c5221 := h 5220 (by decide)
  have h5 : Entails.eval a c4390 := h 4389 (by decide)
  have h6 : Entails.eval a c4561 := h 4560 (by decide)
  have h7 : Entails.eval a c5660 := h 5659 (by decide)
  have h8 : Entails.eval a c4164 := h 4163 (by decide)
  have h9 : Entails.eval a c4141 := h 4140 (by decide)
  have h10 : Entails.eval a c5450 := h 5449 (by decide)
  have h11 : Entails.eval a c3689 := h 3688 (by decide)
  have h12 : Entails.eval a c5943 := derived5943 a h
  have h13 : Entails.eval a c3465 := h 3464 (by decide)
  have h14 : Entails.eval a c5351 := h 5350 (by decide)
  have h15 : Entails.eval a c5985 := derived5985 a h
  have h16 : Entails.eval a c5986 := derived5986 a h
  have h17 : Entails.eval a c4735 := h 4734 (by decide)
  have h18 : Entails.eval a c4669 := h 4668 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5988 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨52, by decide⟩, false), (⟨37, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5988 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4026, some c4192, some c3937, some c4584, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5988 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5988 : lratChecker f5988 p5988 = .success := by decide +kernel
theorem unsat5988 : Unsatisfiable (PosFin 65) f5988 := by
  apply lratCheckerSound f5988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5988
  · intro a ha; simp [p5988] at ha; subst a; trivial
  · exact checked5988
theorem derived5988 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5988 := by
  apply localUnsat_implies_entails f5988 [c4026, c4192, c3937, c4584] c5988 unsat5988 (by rfl) a
  have h0 : Entails.eval a c4026 := h 4025 (by decide)
  have h1 : Entails.eval a c4192 := h 4191 (by decide)
  have h2 : Entails.eval a c3937 := h 3936 (by decide)
  have h3 : Entails.eval a c4584 := h 4583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5989 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5989 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5963, some c5983, some c5984, some c5987, some c5988, some c3488, some c4308, some c3621, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5989 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked5989 : lratChecker f5989 p5989 = .success := by decide +kernel
theorem unsat5989 : Unsatisfiable (PosFin 65) f5989 := by
  apply lratCheckerSound f5989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5989
  · intro a ha; simp [p5989] at ha; subst a; trivial
  · exact checked5989
theorem derived5989 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5989 := by
  apply localUnsat_implies_entails f5989 [c5963, c5983, c5984, c5987, c5988, c3488, c4308, c3621] c5989 unsat5989 (by rfl) a
  have h0 : Entails.eval a c5963 := derived5963 a h
  have h1 : Entails.eval a c5983 := derived5983 a h
  have h2 : Entails.eval a c5984 := derived5984 a h
  have h3 : Entails.eval a c5987 := derived5987 a h
  have h4 : Entails.eval a c5988 := derived5988 a h
  have h5 : Entails.eval a c3488 := h 3487 (by decide)
  have h6 : Entails.eval a c4308 := h 4307 (by decide)
  have h7 : Entails.eval a c3621 := h 3620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5990 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5990 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3488, some c4308, some c3621, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5990 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5990 : lratChecker f5990 p5990 = .success := by decide +kernel
theorem unsat5990 : Unsatisfiable (PosFin 65) f5990 := by
  apply lratCheckerSound f5990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5990
  · intro a ha; simp [p5990] at ha; subst a; trivial
  · exact checked5990
theorem derived5990 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5990 := by
  apply localUnsat_implies_entails f5990 [c3488, c4308, c3621] c5990 unsat5990 (by rfl) a
  have h0 : Entails.eval a c3488 := h 3487 (by decide)
  have h1 : Entails.eval a c4308 := h 4307 (by decide)
  have h2 : Entails.eval a c3621 := h 3620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5991 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨48, by decide⟩, false), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨35, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5991 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2717, some c2814, some c2822, some c3190, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p5991 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5991 : lratChecker f5991 p5991 = .success := by decide +kernel
theorem unsat5991 : Unsatisfiable (PosFin 65) f5991 := by
  apply lratCheckerSound f5991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5991
  · intro a ha; simp [p5991] at ha; subst a; trivial
  · exact checked5991
theorem derived5991 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5991 := by
  apply localUnsat_implies_entails f5991 [c2717, c2814, c2822, c3190] c5991 unsat5991 (by rfl) a
  have h0 : Entails.eval a c2717 := h 2716 (by decide)
  have h1 : Entails.eval a c2814 := h 2813 (by decide)
  have h2 : Entails.eval a c2822 := h 2821 (by decide)
  have h3 : Entails.eval a c3190 := h 3189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5992 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨31, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5992 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3185, some c3009, some c2685, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5992 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5992 : lratChecker f5992 p5992 = .success := by decide +kernel
theorem unsat5992 : Unsatisfiable (PosFin 65) f5992 := by
  apply lratCheckerSound f5992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5992
  · intro a ha; simp [p5992] at ha; subst a; trivial
  · exact checked5992
theorem derived5992 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5992 := by
  apply localUnsat_implies_entails f5992 [c3185, c3009, c2685] c5992 unsat5992 (by rfl) a
  have h0 : Entails.eval a c3185 := h 3184 (by decide)
  have h1 : Entails.eval a c3009 := h 3008 (by decide)
  have h2 : Entails.eval a c2685 := h 2684 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5993 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨46, by decide⟩, false), (⟨34, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5993 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2705, some c2812, some c3127, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p5993 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked5993 : lratChecker f5993 p5993 = .success := by decide +kernel
theorem unsat5993 : Unsatisfiable (PosFin 65) f5993 := by
  apply lratCheckerSound f5993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5993
  · intro a ha; simp [p5993] at ha; subst a; trivial
  · exact checked5993
theorem derived5993 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5993 := by
  apply localUnsat_implies_entails f5993 [c2705, c2812, c3127] c5993 unsat5993 (by rfl) a
  have h0 : Entails.eval a c2705 := h 2704 (by decide)
  have h1 : Entails.eval a c2812 := h 2811 (by decide)
  have h2 : Entails.eval a c3127 := h 3126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c5994 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5994 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5988, some c5990, some c5221, some c4390, some c4561, some c5660, some c5450, some c4141, some c3689, some c3465, some c5351, some c3566, some c5964, some c5943, some c5989, some c4663, some c4821, some c4769, some c4723, some c4669, some c4851, some c5991, some c5993, some c5992, some c2708, some c2818, some c3127, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5994 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked5994 : lratChecker f5994 p5994 = .success := by decide +kernel
theorem unsat5994 : Unsatisfiable (PosFin 65) f5994 := by
  apply lratCheckerSound f5994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5994
  · intro a ha; simp [p5994] at ha; subst a; trivial
  · exact checked5994
theorem derived5994 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5994 := by
  apply localUnsat_implies_entails f5994 [c5988, c5990, c5221, c4390, c4561, c5660, c5450, c4141, c3689, c3465, c5351, c3566, c5964, c5943, c5989, c4663, c4821, c4769, c4723, c4669, c4851, c5991, c5993, c5992, c2708, c2818, c3127] c5994 unsat5994 (by rfl) a
  have h0 : Entails.eval a c5988 := derived5988 a h
  have h1 : Entails.eval a c5990 := derived5990 a h
  have h2 : Entails.eval a c5221 := h 5220 (by decide)
  have h3 : Entails.eval a c4390 := h 4389 (by decide)
  have h4 : Entails.eval a c4561 := h 4560 (by decide)
  have h5 : Entails.eval a c5660 := h 5659 (by decide)
  have h6 : Entails.eval a c5450 := h 5449 (by decide)
  have h7 : Entails.eval a c4141 := h 4140 (by decide)
  have h8 : Entails.eval a c3689 := h 3688 (by decide)
  have h9 : Entails.eval a c3465 := h 3464 (by decide)
  have h10 : Entails.eval a c5351 := h 5350 (by decide)
  have h11 : Entails.eval a c3566 := h 3565 (by decide)
  have h12 : Entails.eval a c5964 := derived5964 a h
  have h13 : Entails.eval a c5943 := derived5943 a h
  have h14 : Entails.eval a c5989 := derived5989 a h
  have h15 : Entails.eval a c4663 := h 4662 (by decide)
  have h16 : Entails.eval a c4821 := h 4820 (by decide)
  have h17 : Entails.eval a c4769 := h 4768 (by decide)
  have h18 : Entails.eval a c4723 := h 4722 (by decide)
  have h19 : Entails.eval a c4669 := h 4668 (by decide)
  have h20 : Entails.eval a c4851 := h 4850 (by decide)
  have h21 : Entails.eval a c5991 := derived5991 a h
  have h22 : Entails.eval a c5993 := derived5993 a h
  have h23 : Entails.eval a c5992 := derived5992 a h
  have h24 : Entails.eval a c2708 := h 2707 (by decide)
  have h25 : Entails.eval a c2818 := h 2817 (by decide)
  have h26 : Entails.eval a c3127 := h 3126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5995 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5995 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5988, some c5990, some c5221, some c4390, some c4561, some c5660, some c5450, some c4141, some c3689, some c3465, some c5351, some c5964, some c5943, some c5989, some c5994, some c3999, some c3990, some c3448, some c3446, some c4896, some c4362, some c5991, some c5993, some c5992, some c2708, some c2818, some c3127, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5995 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked5995 : lratChecker f5995 p5995 = .success := by decide +kernel
theorem unsat5995 : Unsatisfiable (PosFin 65) f5995 := by
  apply lratCheckerSound f5995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5995
  · intro a ha; simp [p5995] at ha; subst a; trivial
  · exact checked5995
theorem derived5995 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5995 := by
  apply localUnsat_implies_entails f5995 [c5988, c5990, c5221, c4390, c4561, c5660, c5450, c4141, c3689, c3465, c5351, c5964, c5943, c5989, c5994, c3999, c3990, c3448, c3446, c4896, c4362, c5991, c5993, c5992, c2708, c2818, c3127] c5995 unsat5995 (by rfl) a
  have h0 : Entails.eval a c5988 := derived5988 a h
  have h1 : Entails.eval a c5990 := derived5990 a h
  have h2 : Entails.eval a c5221 := h 5220 (by decide)
  have h3 : Entails.eval a c4390 := h 4389 (by decide)
  have h4 : Entails.eval a c4561 := h 4560 (by decide)
  have h5 : Entails.eval a c5660 := h 5659 (by decide)
  have h6 : Entails.eval a c5450 := h 5449 (by decide)
  have h7 : Entails.eval a c4141 := h 4140 (by decide)
  have h8 : Entails.eval a c3689 := h 3688 (by decide)
  have h9 : Entails.eval a c3465 := h 3464 (by decide)
  have h10 : Entails.eval a c5351 := h 5350 (by decide)
  have h11 : Entails.eval a c5964 := derived5964 a h
  have h12 : Entails.eval a c5943 := derived5943 a h
  have h13 : Entails.eval a c5989 := derived5989 a h
  have h14 : Entails.eval a c5994 := derived5994 a h
  have h15 : Entails.eval a c3999 := h 3998 (by decide)
  have h16 : Entails.eval a c3990 := h 3989 (by decide)
  have h17 : Entails.eval a c3448 := h 3447 (by decide)
  have h18 : Entails.eval a c3446 := h 3445 (by decide)
  have h19 : Entails.eval a c4896 := h 4895 (by decide)
  have h20 : Entails.eval a c4362 := h 4361 (by decide)
  have h21 : Entails.eval a c5991 := derived5991 a h
  have h22 : Entails.eval a c5993 := derived5993 a h
  have h23 : Entails.eval a c5992 := derived5992 a h
  have h24 : Entails.eval a c2708 := h 2707 (by decide)
  have h25 : Entails.eval a c2818 := h 2817 (by decide)
  have h26 : Entails.eval a c3127 := h 3126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5996 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5996 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5988, some c5990, some c5221, some c4390, some c4561, some c5660, some c4141, some c5450, some c5943, some c5995, some c4744, some c3984, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5996 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked5996 : lratChecker f5996 p5996 = .success := by decide +kernel
theorem unsat5996 : Unsatisfiable (PosFin 65) f5996 := by
  apply lratCheckerSound f5996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5996
  · intro a ha; simp [p5996] at ha; subst a; trivial
  · exact checked5996
theorem derived5996 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5996 := by
  apply localUnsat_implies_entails f5996 [c5988, c5990, c5221, c4390, c4561, c5660, c4141, c5450, c5943, c5995, c4744, c3984] c5996 unsat5996 (by rfl) a
  have h0 : Entails.eval a c5988 := derived5988 a h
  have h1 : Entails.eval a c5990 := derived5990 a h
  have h2 : Entails.eval a c5221 := h 5220 (by decide)
  have h3 : Entails.eval a c4390 := h 4389 (by decide)
  have h4 : Entails.eval a c4561 := h 4560 (by decide)
  have h5 : Entails.eval a c5660 := h 5659 (by decide)
  have h6 : Entails.eval a c4141 := h 4140 (by decide)
  have h7 : Entails.eval a c5450 := h 5449 (by decide)
  have h8 : Entails.eval a c5943 := derived5943 a h
  have h9 : Entails.eval a c5995 := derived5995 a h
  have h10 : Entails.eval a c4744 := h 4743 (by decide)
  have h11 : Entails.eval a c3984 := h 3983 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5997 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5997 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5996, some c5885, some c5943, some c5698, some c5717, some c5221, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p5997 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked5997 : lratChecker f5997 p5997 = .success := by decide +kernel
theorem unsat5997 : Unsatisfiable (PosFin 65) f5997 := by
  apply lratCheckerSound f5997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5997
  · intro a ha; simp [p5997] at ha; subst a; trivial
  · exact checked5997
theorem derived5997 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5997 := by
  apply localUnsat_implies_entails f5997 [c5996, c5885, c5943, c5698, c5717, c5221] c5997 unsat5997 (by rfl) a
  have h0 : Entails.eval a c5996 := derived5996 a h
  have h1 : Entails.eval a c5885 := derived5885 a h
  have h2 : Entails.eval a c5943 := derived5943 a h
  have h3 : Entails.eval a c5698 := h 5697 (by decide)
  have h4 : Entails.eval a c5717 := h 5716 (by decide)
  have h5 : Entails.eval a c5221 := h 5220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c5998 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5998 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5997, some c5921, some c5885, some c5944, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p5998 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5998 : lratChecker f5998 p5998 = .success := by decide +kernel
theorem unsat5998 : Unsatisfiable (PosFin 65) f5998 := by
  apply lratCheckerSound f5998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5998
  · intro a ha; simp [p5998] at ha; subst a; trivial
  · exact checked5998
theorem derived5998 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5998 := by
  apply localUnsat_implies_entails f5998 [c5997, c5921, c5885, c5944] c5998 unsat5998 (by rfl) a
  have h0 : Entails.eval a c5997 := derived5997 a h
  have h1 : Entails.eval a c5921 := derived5921 a h
  have h2 : Entails.eval a c5885 := derived5885 a h
  have h3 : Entails.eval a c5944 := derived5944 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c5999 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f5999 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5997, some c5998, some c5934, some c5945, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p5999 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked5999 : lratChecker f5999 p5999 = .success := by decide +kernel
theorem unsat5999 : Unsatisfiable (PosFin 65) f5999 := by
  apply lratCheckerSound f5999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p5999
  · intro a ha; simp [p5999] at ha; subst a; trivial
  · exact checked5999
theorem derived5999 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c5999 := by
  apply localUnsat_implies_entails f5999 [c5997, c5998, c5934, c5945] c5999 unsat5999 (by rfl) a
  have h0 : Entails.eval a c5997 := derived5997 a h
  have h1 : Entails.eval a c5998 := derived5998 a h
  have h2 : Entails.eval a c5934 := derived5934 a h
  have h3 : Entails.eval a c5945 := derived5945 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6000 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨54, by decide⟩, false), (⟨35, by decide⟩, false), (⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6000 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3440, some c4372, some c3642, some c3645, some c3670, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6000 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6000 : lratChecker f6000 p6000 = .success := by decide +kernel
theorem unsat6000 : Unsatisfiable (PosFin 65) f6000 := by
  apply lratCheckerSound f6000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6000
  · intro a ha; simp [p6000] at ha; subst a; trivial
  · exact checked6000
theorem derived6000 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6000 := by
  apply localUnsat_implies_entails f6000 [c3440, c4372, c3642, c3645, c3670] c6000 unsat6000 (by rfl) a
  have h0 : Entails.eval a c3440 := h 3439 (by decide)
  have h1 : Entails.eval a c4372 := h 4371 (by decide)
  have h2 : Entails.eval a c3642 := h 3641 (by decide)
  have h3 : Entails.eval a c3645 := h 3644 (by decide)
  have h4 : Entails.eval a c3670 := h 3669 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6001 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨35, by decide⟩, false), (⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6001 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6000, some c4744, some c4803, some c4126, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6001 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6001 : lratChecker f6001 p6001 = .success := by decide +kernel
theorem unsat6001 : Unsatisfiable (PosFin 65) f6001 := by
  apply lratCheckerSound f6001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6001
  · intro a ha; simp [p6001] at ha; subst a; trivial
  · exact checked6001
theorem derived6001 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6001 := by
  apply localUnsat_implies_entails f6001 [c6000, c4744, c4803, c4126] c6001 unsat6001 (by rfl) a
  have h0 : Entails.eval a c6000 := derived6000 a h
  have h1 : Entails.eval a c4744 := h 4743 (by decide)
  have h2 : Entails.eval a c4803 := h 4802 (by decide)
  have h3 : Entails.eval a c4126 := h 4125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6002 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨39, by decide⟩, false), (⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6002 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4115, some c4116, some c4120, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6002 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6002 : lratChecker f6002 p6002 = .success := by decide +kernel
theorem unsat6002 : Unsatisfiable (PosFin 65) f6002 := by
  apply lratCheckerSound f6002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6002
  · intro a ha; simp [p6002] at ha; subst a; trivial
  · exact checked6002
theorem derived6002 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6002 := by
  apply localUnsat_implies_entails f6002 [c4115, c4116, c4120] c6002 unsat6002 (by rfl) a
  have h0 : Entails.eval a c4115 := h 4114 (by decide)
  have h1 : Entails.eval a c4116 := h 4115 (by decide)
  have h2 : Entails.eval a c4120 := h 4119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6003 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨54, by decide⟩, true), (⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6003 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6002, some c4810, some c5873, some c5036, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6003 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6003 : lratChecker f6003 p6003 = .success := by decide +kernel
theorem unsat6003 : Unsatisfiable (PosFin 65) f6003 := by
  apply lratCheckerSound f6003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6003
  · intro a ha; simp [p6003] at ha; subst a; trivial
  · exact checked6003
theorem derived6003 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6003 := by
  apply localUnsat_implies_entails f6003 [c6002, c4810, c5873, c5036] c6003 unsat6003 (by rfl) a
  have h0 : Entails.eval a c6002 := derived6002 a h
  have h1 : Entails.eval a c4810 := h 4809 (by decide)
  have h2 : Entails.eval a c5873 := h 5872 (by decide)
  have h3 : Entails.eval a c5036 := h 5035 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6004 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨54, by decide⟩, true), (⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨52, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6004 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5568, some c5560, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6004 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6004 : lratChecker f6004 p6004 = .success := by decide +kernel
theorem unsat6004 : Unsatisfiable (PosFin 65) f6004 := by
  apply lratCheckerSound f6004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6004
  · intro a ha; simp [p6004] at ha; subst a; trivial
  · exact checked6004
theorem derived6004 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6004 := by
  apply localUnsat_implies_entails f6004 [c5568, c5560] c6004 unsat6004 (by rfl) a
  have h0 : Entails.eval a c5568 := h 5567 (by decide)
  have h1 : Entails.eval a c5560 := h 5559 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6005 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨54, by decide⟩, true), (⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6005 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5873, some c5036, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p6005 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6005 : lratChecker f6005 p6005 = .success := by decide +kernel
theorem unsat6005 : Unsatisfiable (PosFin 65) f6005 := by
  apply lratCheckerSound f6005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6005
  · intro a ha; simp [p6005] at ha; subst a; trivial
  · exact checked6005
theorem derived6005 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6005 := by
  apply localUnsat_implies_entails f6005 [c5873, c5036] c6005 unsat6005 (by rfl) a
  have h0 : Entails.eval a c5873 := h 5872 (by decide)
  have h1 : Entails.eval a c5036 := h 5035 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6006 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6006 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6004, some c6003, some c6005, some c3453, some c3655, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6006 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6006 : lratChecker f6006 p6006 = .success := by decide +kernel
theorem unsat6006 : Unsatisfiable (PosFin 65) f6006 := by
  apply lratCheckerSound f6006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6006
  · intro a ha; simp [p6006] at ha; subst a; trivial
  · exact checked6006
theorem derived6006 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6006 := by
  apply localUnsat_implies_entails f6006 [c6004, c6003, c6005, c3453, c3655] c6006 unsat6006 (by rfl) a
  have h0 : Entails.eval a c6004 := derived6004 a h
  have h1 : Entails.eval a c6003 := derived6003 a h
  have h2 : Entails.eval a c6005 := derived6005 a h
  have h3 : Entails.eval a c3453 := h 3452 (by decide)
  have h4 : Entails.eval a c3655 := h 3654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6007 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨52, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6007 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4441, some c4431, some c4436, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6007 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6007 : lratChecker f6007 p6007 = .success := by decide +kernel
theorem unsat6007 : Unsatisfiable (PosFin 65) f6007 := by
  apply lratCheckerSound f6007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6007
  · intro a ha; simp [p6007] at ha; subst a; trivial
  · exact checked6007
theorem derived6007 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6007 := by
  apply localUnsat_implies_entails f6007 [c4441, c4431, c4436] c6007 unsat6007 (by rfl) a
  have h0 : Entails.eval a c4441 := h 4440 (by decide)
  have h1 : Entails.eval a c4431 := h 4430 (by decide)
  have h2 : Entails.eval a c4436 := h 4435 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6008 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨44, by decide⟩, false), (⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6008 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4304, some c3485, some c3743, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p6008 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6008 : lratChecker f6008 p6008 = .success := by decide +kernel
theorem unsat6008 : Unsatisfiable (PosFin 65) f6008 := by
  apply lratCheckerSound f6008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6008
  · intro a ha; simp [p6008] at ha; subst a; trivial
  · exact checked6008
theorem derived6008 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6008 := by
  apply localUnsat_implies_entails f6008 [c4304, c3485, c3743] c6008 unsat6008 (by rfl) a
  have h0 : Entails.eval a c4304 := h 4303 (by decide)
  have h1 : Entails.eval a c3485 := h 3484 (by decide)
  have h2 : Entails.eval a c3743 := h 3742 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6009 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨54, by decide⟩, true), (⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6009 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6008, some c3505, some c3655, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6009 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6009 : lratChecker f6009 p6009 = .success := by decide +kernel
theorem unsat6009 : Unsatisfiable (PosFin 65) f6009 := by
  apply lratCheckerSound f6009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6009
  · intro a ha; simp [p6009] at ha; subst a; trivial
  · exact checked6009
theorem derived6009 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6009 := by
  apply localUnsat_implies_entails f6009 [c6008, c3505, c3655] c6009 unsat6009 (by rfl) a
  have h0 : Entails.eval a c6008 := derived6008 a h
  have h1 : Entails.eval a c3505 := h 3504 (by decide)
  have h2 : Entails.eval a c3655 := h 3654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6010 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨46, by decide⟩, false), (⟨35, by decide⟩, false), (⟨40, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6010 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4354, some c4572, some c4832, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6010 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6010 : lratChecker f6010 p6010 = .success := by decide +kernel
theorem unsat6010 : Unsatisfiable (PosFin 65) f6010 := by
  apply lratCheckerSound f6010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6010
  · intro a ha; simp [p6010] at ha; subst a; trivial
  · exact checked6010
theorem derived6010 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6010 := by
  apply localUnsat_implies_entails f6010 [c4354, c4572, c4832] c6010 unsat6010 (by rfl) a
  have h0 : Entails.eval a c4354 := h 4353 (by decide)
  have h1 : Entails.eval a c4572 := h 4571 (by decide)
  have h2 : Entails.eval a c4832 := h 4831 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6011 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6011 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c5989, some c6007, some c6001, some c6009, some c6006, some c6010, some c4557, some c5805, some c4137, some c3687, some c5964, some c3563, some c5413, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6011 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6011 : lratChecker f6011 p6011 = .success := by decide +kernel
theorem unsat6011 : Unsatisfiable (PosFin 65) f6011 := by
  apply lratCheckerSound f6011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6011
  · intro a ha; simp [p6011] at ha; subst a; trivial
  · exact checked6011
theorem derived6011 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6011 := by
  apply localUnsat_implies_entails f6011 [c5999, c5989, c6007, c6001, c6009, c6006, c6010, c4557, c5805, c4137, c3687, c5964, c3563, c5413] c6011 unsat6011 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c5989 := derived5989 a h
  have h2 : Entails.eval a c6007 := derived6007 a h
  have h3 : Entails.eval a c6001 := derived6001 a h
  have h4 : Entails.eval a c6009 := derived6009 a h
  have h5 : Entails.eval a c6006 := derived6006 a h
  have h6 : Entails.eval a c6010 := derived6010 a h
  have h7 : Entails.eval a c4557 := h 4556 (by decide)
  have h8 : Entails.eval a c5805 := h 5804 (by decide)
  have h9 : Entails.eval a c4137 := h 4136 (by decide)
  have h10 : Entails.eval a c3687 := h 3686 (by decide)
  have h11 : Entails.eval a c5964 := derived5964 a h
  have h12 : Entails.eval a c3563 := h 3562 (by decide)
  have h13 : Entails.eval a c5413 := h 5412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6012 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨54, by decide⟩, true), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6012 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4217, some c5240, some c5633, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p6012 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6012 : lratChecker f6012 p6012 = .success := by decide +kernel
theorem unsat6012 : Unsatisfiable (PosFin 65) f6012 := by
  apply lratCheckerSound f6012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6012
  · intro a ha; simp [p6012] at ha; subst a; trivial
  · exact checked6012
theorem derived6012 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6012 := by
  apply localUnsat_implies_entails f6012 [c4217, c5240, c5633] c6012 unsat6012 (by rfl) a
  have h0 : Entails.eval a c4217 := h 4216 (by decide)
  have h1 : Entails.eval a c5240 := h 5239 (by decide)
  have h2 : Entails.eval a c5633 := h 5632 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6013 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6013 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4295, some c3990, some c4228, some c4848, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6013 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6013 : lratChecker f6013 p6013 = .success := by decide +kernel
theorem unsat6013 : Unsatisfiable (PosFin 65) f6013 := by
  apply lratCheckerSound f6013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6013
  · intro a ha; simp [p6013] at ha; subst a; trivial
  · exact checked6013
theorem derived6013 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6013 := by
  apply localUnsat_implies_entails f6013 [c4295, c3990, c4228, c4848] c6013 unsat6013 (by rfl) a
  have h0 : Entails.eval a c4295 := h 4294 (by decide)
  have h1 : Entails.eval a c3990 := h 3989 (by decide)
  have h2 : Entails.eval a c4228 := h 4227 (by decide)
  have h3 : Entails.eval a c4848 := h 4847 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6014 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6014 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6013, some c6012, some c5251, some c4225, some c4293, some c5634, some c5636, some c5748, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6014 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6014 : lratChecker f6014 p6014 = .success := by decide +kernel
theorem unsat6014 : Unsatisfiable (PosFin 65) f6014 := by
  apply lratCheckerSound f6014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6014
  · intro a ha; simp [p6014] at ha; subst a; trivial
  · exact checked6014
theorem derived6014 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6014 := by
  apply localUnsat_implies_entails f6014 [c6013, c6012, c5251, c4225, c4293, c5634, c5636, c5748] c6014 unsat6014 (by rfl) a
  have h0 : Entails.eval a c6013 := derived6013 a h
  have h1 : Entails.eval a c6012 := derived6012 a h
  have h2 : Entails.eval a c5251 := h 5250 (by decide)
  have h3 : Entails.eval a c4225 := h 4224 (by decide)
  have h4 : Entails.eval a c4293 := h 4292 (by decide)
  have h5 : Entails.eval a c5634 := h 5633 (by decide)
  have h6 : Entails.eval a c5636 := h 5635 (by decide)
  have h7 : Entails.eval a c5748 := h 5747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6015 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6015 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5642, some c4803, some c4525, some c4372, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6015 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6015 : lratChecker f6015 p6015 = .success := by decide +kernel
theorem unsat6015 : Unsatisfiable (PosFin 65) f6015 := by
  apply lratCheckerSound f6015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6015
  · intro a ha; simp [p6015] at ha; subst a; trivial
  · exact checked6015
theorem derived6015 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6015 := by
  apply localUnsat_implies_entails f6015 [c5642, c4803, c4525, c4372] c6015 unsat6015 (by rfl) a
  have h0 : Entails.eval a c5642 := h 5641 (by decide)
  have h1 : Entails.eval a c4803 := h 4802 (by decide)
  have h2 : Entails.eval a c4525 := h 4524 (by decide)
  have h3 : Entails.eval a c4372 := h 4371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6016 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨59, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6016 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c5989, some c6015, some c5610, some c4137, some c5560, some c5452, some c5445, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6016 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6016 : lratChecker f6016 p6016 = .success := by decide +kernel
theorem unsat6016 : Unsatisfiable (PosFin 65) f6016 := by
  apply lratCheckerSound f6016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6016
  · intro a ha; simp [p6016] at ha; subst a; trivial
  · exact checked6016
theorem derived6016 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6016 := by
  apply localUnsat_implies_entails f6016 [c5999, c5989, c6015, c5610, c4137, c5560, c5452, c5445] c6016 unsat6016 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c5989 := derived5989 a h
  have h2 : Entails.eval a c6015 := derived6015 a h
  have h3 : Entails.eval a c5610 := h 5609 (by decide)
  have h4 : Entails.eval a c4137 := h 4136 (by decide)
  have h5 : Entails.eval a c5560 := h 5559 (by decide)
  have h6 : Entails.eval a c5452 := h 5451 (by decide)
  have h7 : Entails.eval a c5445 := h 5444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6017 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨59, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6017 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c6014, some c6011, some c6016, some c6008, some c3497, some c5642, some c3697, some c5043, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6017 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6017 : lratChecker f6017 p6017 = .success := by decide +kernel
theorem unsat6017 : Unsatisfiable (PosFin 65) f6017 := by
  apply lratCheckerSound f6017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6017
  · intro a ha; simp [p6017] at ha; subst a; trivial
  · exact checked6017
theorem derived6017 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6017 := by
  apply localUnsat_implies_entails f6017 [c5999, c6014, c6011, c6016, c6008, c3497, c5642, c3697, c5043] c6017 unsat6017 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c6014 := derived6014 a h
  have h2 : Entails.eval a c6011 := derived6011 a h
  have h3 : Entails.eval a c6016 := derived6016 a h
  have h4 : Entails.eval a c6008 := derived6008 a h
  have h5 : Entails.eval a c3497 := h 3496 (by decide)
  have h6 : Entails.eval a c5642 := h 5641 (by decide)
  have h7 : Entails.eval a c3697 := h 3696 (by decide)
  have h8 : Entails.eval a c5043 := h 5042 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6018 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6018 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4126, some c3697, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6018 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6018 : lratChecker f6018 p6018 = .success := by decide +kernel
theorem unsat6018 : Unsatisfiable (PosFin 65) f6018 := by
  apply lratCheckerSound f6018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6018
  · intro a ha; simp [p6018] at ha; subst a; trivial
  · exact checked6018
theorem derived6018 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6018 := by
  apply localUnsat_implies_entails f6018 [c4126, c3697] c6018 unsat6018 (by rfl) a
  have h0 : Entails.eval a c4126 := h 4125 (by decide)
  have h1 : Entails.eval a c3697 := h 3696 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6019 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6019 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c6017, some c5953, some c6018, some c4116, some c3687, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6019 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6019 : lratChecker f6019 p6019 = .success := by decide +kernel
theorem unsat6019 : Unsatisfiable (PosFin 65) f6019 := by
  apply lratCheckerSound f6019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6019
  · intro a ha; simp [p6019] at ha; subst a; trivial
  · exact checked6019
theorem derived6019 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6019 := by
  apply localUnsat_implies_entails f6019 [c5999, c6017, c5953, c6018, c4116, c3687] c6019 unsat6019 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c6017 := derived6017 a h
  have h2 : Entails.eval a c5953 := derived5953 a h
  have h3 : Entails.eval a c6018 := derived6018 a h
  have h4 : Entails.eval a c4116 := h 4115 (by decide)
  have h5 : Entails.eval a c3687 := h 3686 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6020 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨34, by decide⟩, false), (⟨64, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6020 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6011, some c6019, some c4974, some c4748, some c3714, some c3453, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6020 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6020 : lratChecker f6020 p6020 = .success := by decide +kernel
theorem unsat6020 : Unsatisfiable (PosFin 65) f6020 := by
  apply lratCheckerSound f6020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6020
  · intro a ha; simp [p6020] at ha; subst a; trivial
  · exact checked6020
theorem derived6020 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6020 := by
  apply localUnsat_implies_entails f6020 [c6011, c6019, c4974, c4748, c3714, c3453] c6020 unsat6020 (by rfl) a
  have h0 : Entails.eval a c6011 := derived6011 a h
  have h1 : Entails.eval a c6019 := derived6019 a h
  have h2 : Entails.eval a c4974 := h 4973 (by decide)
  have h3 : Entails.eval a c4748 := h 4747 (by decide)
  have h4 : Entails.eval a c3714 := h 3713 (by decide)
  have h5 : Entails.eval a c3453 := h 3452 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6021 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6021 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c6014, some c6020, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6021 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6021 : lratChecker f6021 p6021 = .success := by decide +kernel
theorem unsat6021 : Unsatisfiable (PosFin 65) f6021 := by
  apply lratCheckerSound f6021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6021
  · intro a ha; simp [p6021] at ha; subst a; trivial
  · exact checked6021
theorem derived6021 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6021 := by
  apply localUnsat_implies_entails f6021 [c5999, c6014, c6020] c6021 unsat6021 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c6014 := derived6014 a h
  have h2 : Entails.eval a c6020 := derived6020 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6022 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨59, by decide⟩, false), (⟨45, by decide⟩, true), (⟨40, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6022 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4748, some c3714, some c4473, some c3528, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6022 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6022 : lratChecker f6022 p6022 = .success := by decide +kernel
theorem unsat6022 : Unsatisfiable (PosFin 65) f6022 := by
  apply lratCheckerSound f6022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6022
  · intro a ha; simp [p6022] at ha; subst a; trivial
  · exact checked6022
theorem derived6022 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6022 := by
  apply localUnsat_implies_entails f6022 [c4748, c3714, c4473, c3528] c6022 unsat6022 (by rfl) a
  have h0 : Entails.eval a c4748 := h 4747 (by decide)
  have h1 : Entails.eval a c3714 := h 3713 (by decide)
  have h2 : Entails.eval a c4473 := h 4472 (by decide)
  have h3 : Entails.eval a c3528 := h 3527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6023 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨45, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6023 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4173, some c6022, some c4974, some c6007, some c3655, some c3557, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6023 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6023 : lratChecker f6023 p6023 = .success := by decide +kernel
theorem unsat6023 : Unsatisfiable (PosFin 65) f6023 := by
  apply lratCheckerSound f6023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6023
  · intro a ha; simp [p6023] at ha; subst a; trivial
  · exact checked6023
theorem derived6023 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6023 := by
  apply localUnsat_implies_entails f6023 [c4173, c6022, c4974, c6007, c3655, c3557] c6023 unsat6023 (by rfl) a
  have h0 : Entails.eval a c4173 := h 4172 (by decide)
  have h1 : Entails.eval a c6022 := derived6022 a h
  have h2 : Entails.eval a c4974 := h 4973 (by decide)
  have h3 : Entails.eval a c6007 := derived6007 a h
  have h4 : Entails.eval a c3655 := h 3654 (by decide)
  have h5 : Entails.eval a c3557 := h 3556 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6024 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨52, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6024 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3535, some c3547, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6024 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6024 : lratChecker f6024 p6024 = .success := by decide +kernel
theorem unsat6024 : Unsatisfiable (PosFin 65) f6024 := by
  apply lratCheckerSound f6024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6024
  · intro a ha; simp [p6024] at ha; subst a; trivial
  · exact checked6024
theorem derived6024 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6024 := by
  apply localUnsat_implies_entails f6024 [c3535, c3547] c6024 unsat6024 (by rfl) a
  have h0 : Entails.eval a c3535 := h 3534 (by decide)
  have h1 : Entails.eval a c3547 := h 3546 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6025 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6025 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4163, some c4171, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6025 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6025 : lratChecker f6025 p6025 = .success := by decide +kernel
theorem unsat6025 : Unsatisfiable (PosFin 65) f6025 := by
  apply lratCheckerSound f6025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6025
  · intro a ha; simp [p6025] at ha; subst a; trivial
  · exact checked6025
theorem derived6025 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6025 := by
  apply localUnsat_implies_entails f6025 [c4163, c4171] c6025 unsat6025 (by rfl) a
  have h0 : Entails.eval a c4163 := h 4162 (by decide)
  have h1 : Entails.eval a c4171 := h 4170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6026 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨45, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6026 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6025, some c5929, some c4972, some c3861, some c4449, some c5516, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6026 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6026 : lratChecker f6026 p6026 = .success := by decide +kernel
theorem unsat6026 : Unsatisfiable (PosFin 65) f6026 := by
  apply lratCheckerSound f6026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6026
  · intro a ha; simp [p6026] at ha; subst a; trivial
  · exact checked6026
theorem derived6026 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6026 := by
  apply localUnsat_implies_entails f6026 [c6025, c5929, c4972, c3861, c4449, c5516] c6026 unsat6026 (by rfl) a
  have h0 : Entails.eval a c6025 := derived6025 a h
  have h1 : Entails.eval a c5929 := derived5929 a h
  have h2 : Entails.eval a c4972 := h 4971 (by decide)
  have h3 : Entails.eval a c3861 := h 3860 (by decide)
  have h4 : Entails.eval a c4449 := h 4448 (by decide)
  have h5 : Entails.eval a c5516 := h 5515 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6027 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨35, by decide⟩, true), (⟨62, by decide⟩, false), (⟨33, by decide⟩, false), (⟨45, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6027 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6026, some c4963, some c4465, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p6027 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6027 : lratChecker f6027 p6027 = .success := by decide +kernel
theorem unsat6027 : Unsatisfiable (PosFin 65) f6027 := by
  apply lratCheckerSound f6027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6027
  · intro a ha; simp [p6027] at ha; subst a; trivial
  · exact checked6027
theorem derived6027 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6027 := by
  apply localUnsat_implies_entails f6027 [c6026, c4963, c4465] c6027 unsat6027 (by rfl) a
  have h0 : Entails.eval a c6026 := derived6026 a h
  have h1 : Entails.eval a c4963 := h 4962 (by decide)
  have h2 : Entails.eval a c4465 := h 4464 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6028 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨45, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6028 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c6021, some c6023, some c5989, some c6025, some c6024, some c6007, some c6027, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6028 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6028 : lratChecker f6028 p6028 = .success := by decide +kernel
theorem unsat6028 : Unsatisfiable (PosFin 65) f6028 := by
  apply lratCheckerSound f6028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6028
  · intro a ha; simp [p6028] at ha; subst a; trivial
  · exact checked6028
theorem derived6028 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6028 := by
  apply localUnsat_implies_entails f6028 [c5999, c6021, c6023, c5989, c6025, c6024, c6007, c6027] c6028 unsat6028 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c6021 := derived6021 a h
  have h2 : Entails.eval a c6023 := derived6023 a h
  have h3 : Entails.eval a c5989 := derived5989 a h
  have h4 : Entails.eval a c6025 := derived6025 a h
  have h5 : Entails.eval a c6024 := derived6024 a h
  have h6 : Entails.eval a c6007 := derived6007 a h
  have h7 : Entails.eval a c6027 := derived6027 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6029 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6029 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3706, some c4963, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6029 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6029 : lratChecker f6029 p6029 = .success := by decide +kernel
theorem unsat6029 : Unsatisfiable (PosFin 65) f6029 := by
  apply lratCheckerSound f6029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6029
  · intro a ha; simp [p6029] at ha; subst a; trivial
  · exact checked6029
theorem derived6029 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6029 := by
  apply localUnsat_implies_entails f6029 [c3706, c4963] c6029 unsat6029 (by rfl) a
  have h0 : Entails.eval a c3706 := h 3705 (by decide)
  have h1 : Entails.eval a c4963 := h 4962 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6030 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6030 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6029, some c3698, some c4972, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6030 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6030 : lratChecker f6030 p6030 = .success := by decide +kernel
theorem unsat6030 : Unsatisfiable (PosFin 65) f6030 := by
  apply lratCheckerSound f6030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6030
  · intro a ha; simp [p6030] at ha; subst a; trivial
  · exact checked6030
theorem derived6030 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6030 := by
  apply localUnsat_implies_entails f6030 [c6029, c3698, c4972] c6030 unsat6030 (by rfl) a
  have h0 : Entails.eval a c6029 := derived6029 a h
  have h1 : Entails.eval a c3698 := h 3697 (by decide)
  have h2 : Entails.eval a c4972 := h 4971 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6031 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6031 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c5989, some c6028, some c6030, some c3644, some c3652, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6031 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6031 : lratChecker f6031 p6031 = .success := by decide +kernel
theorem unsat6031 : Unsatisfiable (PosFin 65) f6031 := by
  apply lratCheckerSound f6031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6031
  · intro a ha; simp [p6031] at ha; subst a; trivial
  · exact checked6031
theorem derived6031 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6031 := by
  apply localUnsat_implies_entails f6031 [c5999, c5989, c6028, c6030, c3644, c3652] c6031 unsat6031 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c5989 := derived5989 a h
  have h2 : Entails.eval a c6028 := derived6028 a h
  have h3 : Entails.eval a c6030 := derived6030 a h
  have h4 : Entails.eval a c3644 := h 3643 (by decide)
  have h5 : Entails.eval a c3652 := h 3651 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6032 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨33, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6032 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5243, some c3777, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6032 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6032 : lratChecker f6032 p6032 = .success := by decide +kernel
theorem unsat6032 : Unsatisfiable (PosFin 65) f6032 := by
  apply lratCheckerSound f6032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6032
  · intro a ha; simp [p6032] at ha; subst a; trivial
  · exact checked6032
theorem derived6032 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6032 := by
  apply localUnsat_implies_entails f6032 [c5243, c3777] c6032 unsat6032 (by rfl) a
  have h0 : Entails.eval a c5243 := h 5242 (by decide)
  have h1 : Entails.eval a c3777 := h 3776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6033 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨45, by decide⟩, false), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6033 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6025, some c6032, some c4203, some c3698, some c5498, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6033 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6033 : lratChecker f6033 p6033 = .success := by decide +kernel
theorem unsat6033 : Unsatisfiable (PosFin 65) f6033 := by
  apply lratCheckerSound f6033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6033
  · intro a ha; simp [p6033] at ha; subst a; trivial
  · exact checked6033
theorem derived6033 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6033 := by
  apply localUnsat_implies_entails f6033 [c6025, c6032, c4203, c3698, c5498] c6033 unsat6033 (by rfl) a
  have h0 : Entails.eval a c6025 := derived6025 a h
  have h1 : Entails.eval a c6032 := derived6032 a h
  have h2 : Entails.eval a c4203 := h 4202 (by decide)
  have h3 : Entails.eval a c3698 := h 3697 (by decide)
  have h4 : Entails.eval a c5498 := h 5497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6034 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6034 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5989, some c5999, some c6021, some c6031, some c6033, some c6025, some c4203, some c5900, some c4593, some c3861, some c5498, some c5244, some c4456, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6034 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6034 : lratChecker f6034 p6034 = .success := by decide +kernel
theorem unsat6034 : Unsatisfiable (PosFin 65) f6034 := by
  apply lratCheckerSound f6034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6034
  · intro a ha; simp [p6034] at ha; subst a; trivial
  · exact checked6034
theorem derived6034 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6034 := by
  apply localUnsat_implies_entails f6034 [c5989, c5999, c6021, c6031, c6033, c6025, c4203, c5900, c4593, c3861, c5498, c5244, c4456] c6034 unsat6034 (by rfl) a
  have h0 : Entails.eval a c5989 := derived5989 a h
  have h1 : Entails.eval a c5999 := derived5999 a h
  have h2 : Entails.eval a c6021 := derived6021 a h
  have h3 : Entails.eval a c6031 := derived6031 a h
  have h4 : Entails.eval a c6033 := derived6033 a h
  have h5 : Entails.eval a c6025 := derived6025 a h
  have h6 : Entails.eval a c4203 := h 4202 (by decide)
  have h7 : Entails.eval a c5900 := derived5900 a h
  have h8 : Entails.eval a c4593 := h 4592 (by decide)
  have h9 : Entails.eval a c3861 := h 3860 (by decide)
  have h10 : Entails.eval a c5498 := h 5497 (by decide)
  have h11 : Entails.eval a c5244 := h 5243 (by decide)
  have h12 : Entails.eval a c4456 := h 4455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6035 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6035 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c5989, some c6021, some c6031, some c6034, some c5243, some c4190, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6035 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6035 : lratChecker f6035 p6035 = .success := by decide +kernel
theorem unsat6035 : Unsatisfiable (PosFin 65) f6035 := by
  apply lratCheckerSound f6035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6035
  · intro a ha; simp [p6035] at ha; subst a; trivial
  · exact checked6035
theorem derived6035 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6035 := by
  apply localUnsat_implies_entails f6035 [c5999, c5989, c6021, c6031, c6034, c5243, c4190] c6035 unsat6035 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c5989 := derived5989 a h
  have h2 : Entails.eval a c6021 := derived6021 a h
  have h3 : Entails.eval a c6031 := derived6031 a h
  have h4 : Entails.eval a c6034 := derived6034 a h
  have h5 : Entails.eval a c5243 := h 5242 (by decide)
  have h6 : Entails.eval a c4190 := h 4189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6036 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6036 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5094, some c5103, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6036 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6036 : lratChecker f6036 p6036 = .success := by decide +kernel
theorem unsat6036 : Unsatisfiable (PosFin 65) f6036 := by
  apply lratCheckerSound f6036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6036
  · intro a ha; simp [p6036] at ha; subst a; trivial
  · exact checked6036
theorem derived6036 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6036 := by
  apply localUnsat_implies_entails f6036 [c5094, c5103] c6036 unsat6036 (by rfl) a
  have h0 : Entails.eval a c5094 := h 5093 (by decide)
  have h1 : Entails.eval a c5103 := h 5102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6037 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6037 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5075, some c4993, some c5419, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6037 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6037 : lratChecker f6037 p6037 = .success := by decide +kernel
theorem unsat6037 : Unsatisfiable (PosFin 65) f6037 := by
  apply lratCheckerSound f6037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6037
  · intro a ha; simp [p6037] at ha; subst a; trivial
  · exact checked6037
theorem derived6037 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6037 := by
  apply localUnsat_implies_entails f6037 [c5075, c4993, c5419] c6037 unsat6037 (by rfl) a
  have h0 : Entails.eval a c5075 := h 5074 (by decide)
  have h1 : Entails.eval a c4993 := h 4992 (by decide)
  have h2 : Entails.eval a c5419 := h 5418 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6038 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨64, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6038 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6036, some c6037, some c4987, some c5067, some c5412, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6038 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6038 : lratChecker f6038 p6038 = .success := by decide +kernel
theorem unsat6038 : Unsatisfiable (PosFin 65) f6038 := by
  apply lratCheckerSound f6038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6038
  · intro a ha; simp [p6038] at ha; subst a; trivial
  · exact checked6038
theorem derived6038 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6038 := by
  apply localUnsat_implies_entails f6038 [c6036, c6037, c4987, c5067, c5412] c6038 unsat6038 (by rfl) a
  have h0 : Entails.eval a c6036 := derived6036 a h
  have h1 : Entails.eval a c6037 := derived6037 a h
  have h2 : Entails.eval a c4987 := h 4986 (by decide)
  have h3 : Entails.eval a c5067 := h 5066 (by decide)
  have h4 : Entails.eval a c5412 := h 5411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6039 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6039 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5999, some c5989, some c6035, some c6038, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6039 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6039 : lratChecker f6039 p6039 = .success := by decide +kernel
theorem unsat6039 : Unsatisfiable (PosFin 65) f6039 := by
  apply lratCheckerSound f6039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6039
  · intro a ha; simp [p6039] at ha; subst a; trivial
  · exact checked6039
theorem derived6039 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6039 := by
  apply localUnsat_implies_entails f6039 [c5999, c5989, c6035, c6038] c6039 unsat6039 (by rfl) a
  have h0 : Entails.eval a c5999 := derived5999 a h
  have h1 : Entails.eval a c5989 := derived5989 a h
  have h2 : Entails.eval a c6035 := derived6035 a h
  have h3 : Entails.eval a c6038 := derived6038 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6040 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6040 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3503, some c4396, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6040 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6040 : lratChecker f6040 p6040 = .success := by decide +kernel
theorem unsat6040 : Unsatisfiable (PosFin 65) f6040 := by
  apply lratCheckerSound f6040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6040
  · intro a ha; simp [p6040] at ha; subst a; trivial
  · exact checked6040
theorem derived6040 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6040 := by
  apply localUnsat_implies_entails f6040 [c3503, c4396] c6040 unsat6040 (by rfl) a
  have h0 : Entails.eval a c3503 := h 3502 (by decide)
  have h1 : Entails.eval a c4396 := h 4395 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6041 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨55, by decide⟩, true), (⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6041 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5412, some c5787, some c5329, some c4053, some c3588, some c3537, some c6040, some c5271, some c5518, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6041 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6041 : lratChecker f6041 p6041 = .success := by decide +kernel
theorem unsat6041 : Unsatisfiable (PosFin 65) f6041 := by
  apply lratCheckerSound f6041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6041
  · intro a ha; simp [p6041] at ha; subst a; trivial
  · exact checked6041
theorem derived6041 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6041 := by
  apply localUnsat_implies_entails f6041 [c5412, c5787, c5329, c4053, c3588, c3537, c6040, c5271, c5518] c6041 unsat6041 (by rfl) a
  have h0 : Entails.eval a c5412 := h 5411 (by decide)
  have h1 : Entails.eval a c5787 := h 5786 (by decide)
  have h2 : Entails.eval a c5329 := h 5328 (by decide)
  have h3 : Entails.eval a c4053 := h 4052 (by decide)
  have h4 : Entails.eval a c3588 := h 3587 (by decide)
  have h5 : Entails.eval a c3537 := h 3536 (by decide)
  have h6 : Entails.eval a c6040 := derived6040 a h
  have h7 : Entails.eval a c5271 := h 5270 (by decide)
  have h8 : Entails.eval a c5518 := h 5517 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6042 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6042 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6039, some c5999, some c5989, some c6041, some c4481, some c6007, some c4631, some c3935, some c5329, some c3588, some c6040, some c4465, some c4139, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6042 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6042 : lratChecker f6042 p6042 = .success := by decide +kernel
theorem unsat6042 : Unsatisfiable (PosFin 65) f6042 := by
  apply lratCheckerSound f6042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6042
  · intro a ha; simp [p6042] at ha; subst a; trivial
  · exact checked6042
theorem derived6042 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6042 := by
  apply localUnsat_implies_entails f6042 [c6039, c5999, c5989, c6041, c4481, c6007, c4631, c3935, c5329, c3588, c6040, c4465, c4139] c6042 unsat6042 (by rfl) a
  have h0 : Entails.eval a c6039 := derived6039 a h
  have h1 : Entails.eval a c5999 := derived5999 a h
  have h2 : Entails.eval a c5989 := derived5989 a h
  have h3 : Entails.eval a c6041 := derived6041 a h
  have h4 : Entails.eval a c4481 := h 4480 (by decide)
  have h5 : Entails.eval a c6007 := derived6007 a h
  have h6 : Entails.eval a c4631 := h 4630 (by decide)
  have h7 : Entails.eval a c3935 := h 3934 (by decide)
  have h8 : Entails.eval a c5329 := h 5328 (by decide)
  have h9 : Entails.eval a c3588 := h 3587 (by decide)
  have h10 : Entails.eval a c6040 := derived6040 a h
  have h11 : Entails.eval a c4465 := h 4464 (by decide)
  have h12 : Entails.eval a c4139 := h 4138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6043 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, false), (⟨37, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6043 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3500, some c3446, some c4686, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6043 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6043 : lratChecker f6043 p6043 = .success := by decide +kernel
theorem unsat6043 : Unsatisfiable (PosFin 65) f6043 := by
  apply lratCheckerSound f6043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6043
  · intro a ha; simp [p6043] at ha; subst a; trivial
  · exact checked6043
theorem derived6043 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6043 := by
  apply localUnsat_implies_entails f6043 [c3500, c3446, c4686] c6043 unsat6043 (by rfl) a
  have h0 : Entails.eval a c3500 := h 3499 (by decide)
  have h1 : Entails.eval a c3446 := h 3445 (by decide)
  have h2 : Entails.eval a c4686 := h 4685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6044 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨57, by decide⟩, true), (⟨55, by decide⟩, false), (⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6044 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3589, some c3652, some c5330, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6044 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6044 : lratChecker f6044 p6044 = .success := by decide +kernel
theorem unsat6044 : Unsatisfiable (PosFin 65) f6044 := by
  apply lratCheckerSound f6044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6044
  · intro a ha; simp [p6044] at ha; subst a; trivial
  · exact checked6044
theorem derived6044 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6044 := by
  apply localUnsat_implies_entails f6044 [c3589, c3652, c5330] c6044 unsat6044 (by rfl) a
  have h0 : Entails.eval a c3589 := h 3588 (by decide)
  have h1 : Entails.eval a c3652 := h 3651 (by decide)
  have h2 : Entails.eval a c5330 := h 5329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6045 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false), (⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6045 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6044, some c6043, some c4055, some c3936, some c4512, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6045 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6045 : lratChecker f6045 p6045 = .success := by decide +kernel
theorem unsat6045 : Unsatisfiable (PosFin 65) f6045 := by
  apply lratCheckerSound f6045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6045
  · intro a ha; simp [p6045] at ha; subst a; trivial
  · exact checked6045
theorem derived6045 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6045 := by
  apply localUnsat_implies_entails f6045 [c6044, c6043, c4055, c3936, c4512] c6045 unsat6045 (by rfl) a
  have h0 : Entails.eval a c6044 := derived6044 a h
  have h1 : Entails.eval a c6043 := derived6043 a h
  have h2 : Entails.eval a c4055 := h 4054 (by decide)
  have h3 : Entails.eval a c3936 := h 3935 (by decide)
  have h4 : Entails.eval a c4512 := h 4511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6046 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6046 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5989, some c5999, some c6039, some c6042, some c6045, some c3948, some c4062, some c4512, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6046 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6046 : lratChecker f6046 p6046 = .success := by decide +kernel
theorem unsat6046 : Unsatisfiable (PosFin 65) f6046 := by
  apply lratCheckerSound f6046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6046
  · intro a ha; simp [p6046] at ha; subst a; trivial
  · exact checked6046
theorem derived6046 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6046 := by
  apply localUnsat_implies_entails f6046 [c5989, c5999, c6039, c6042, c6045, c3948, c4062, c4512] c6046 unsat6046 (by rfl) a
  have h0 : Entails.eval a c5989 := derived5989 a h
  have h1 : Entails.eval a c5999 := derived5999 a h
  have h2 : Entails.eval a c6039 := derived6039 a h
  have h3 : Entails.eval a c6042 := derived6042 a h
  have h4 : Entails.eval a c6045 := derived6045 a h
  have h5 : Entails.eval a c3948 := h 3947 (by decide)
  have h6 : Entails.eval a c4062 := h 4061 (by decide)
  have h7 : Entails.eval a c4512 := h 4511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6047 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6047 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6039, some c6042, some c6046, some c6043, some c3652, some c3597, some c5336, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6047 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6047 : lratChecker f6047 p6047 = .success := by decide +kernel
theorem unsat6047 : Unsatisfiable (PosFin 65) f6047 := by
  apply lratCheckerSound f6047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6047
  · intro a ha; simp [p6047] at ha; subst a; trivial
  · exact checked6047
theorem derived6047 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6047 := by
  apply localUnsat_implies_entails f6047 [c6039, c6042, c6046, c6043, c3652, c3597, c5336] c6047 unsat6047 (by rfl) a
  have h0 : Entails.eval a c6039 := derived6039 a h
  have h1 : Entails.eval a c6042 := derived6042 a h
  have h2 : Entails.eval a c6046 := derived6046 a h
  have h3 : Entails.eval a c6043 := derived6043 a h
  have h4 : Entails.eval a c3652 := h 3651 (by decide)
  have h5 : Entails.eval a c3597 := h 3596 (by decide)
  have h6 : Entails.eval a c5336 := h 5335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6048 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6048 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5721, some c5704, some c5223, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6048 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6048 : lratChecker f6048 p6048 = .success := by decide +kernel
theorem unsat6048 : Unsatisfiable (PosFin 65) f6048 := by
  apply lratCheckerSound f6048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6048
  · intro a ha; simp [p6048] at ha; subst a; trivial
  · exact checked6048
theorem derived6048 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6048 := by
  apply localUnsat_implies_entails f6048 [c5721, c5704, c5223] c6048 unsat6048 (by rfl) a
  have h0 : Entails.eval a c5721 := h 5720 (by decide)
  have h1 : Entails.eval a c5704 := h 5703 (by decide)
  have h2 : Entails.eval a c5223 := h 5222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6049 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6049 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6039, some c5999, some c5989, some c6047, some c6048, some c5716, some c4053, some c3588, some c6013, some c5217, some c3487, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6049 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6049 : lratChecker f6049 p6049 = .success := by decide +kernel
theorem unsat6049 : Unsatisfiable (PosFin 65) f6049 := by
  apply lratCheckerSound f6049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6049
  · intro a ha; simp [p6049] at ha; subst a; trivial
  · exact checked6049
theorem derived6049 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6049 := by
  apply localUnsat_implies_entails f6049 [c6039, c5999, c5989, c6047, c6048, c5716, c4053, c3588, c6013, c5217, c3487] c6049 unsat6049 (by rfl) a
  have h0 : Entails.eval a c6039 := derived6039 a h
  have h1 : Entails.eval a c5999 := derived5999 a h
  have h2 : Entails.eval a c5989 := derived5989 a h
  have h3 : Entails.eval a c6047 := derived6047 a h
  have h4 : Entails.eval a c6048 := derived6048 a h
  have h5 : Entails.eval a c5716 := h 5715 (by decide)
  have h6 : Entails.eval a c4053 := h 4052 (by decide)
  have h7 : Entails.eval a c3588 := h 3587 (by decide)
  have h8 : Entails.eval a c6013 := derived6013 a h
  have h9 : Entails.eval a c5217 := h 5216 (by decide)
  have h10 : Entails.eval a c3487 := h 3486 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6050 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨45, by decide⟩, false), (⟨55, by decide⟩, true), (⟨37, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6050 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4053, some c3588, some c6013, some c5217, some c3487, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6050 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6050 : lratChecker f6050 p6050 = .success := by decide +kernel
theorem unsat6050 : Unsatisfiable (PosFin 65) f6050 := by
  apply lratCheckerSound f6050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6050
  · intro a ha; simp [p6050] at ha; subst a; trivial
  · exact checked6050
theorem derived6050 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6050 := by
  apply localUnsat_implies_entails f6050 [c4053, c3588, c6013, c5217, c3487] c6050 unsat6050 (by rfl) a
  have h0 : Entails.eval a c4053 := h 4052 (by decide)
  have h1 : Entails.eval a c3588 := h 3587 (by decide)
  have h2 : Entails.eval a c6013 := derived6013 a h
  have h3 : Entails.eval a c5217 := h 5216 (by decide)
  have h4 : Entails.eval a c3487 := h 3486 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6051 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨58, by decide⟩, true), (⟨49, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6051 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2709, some c2820, some c2826, some c3127, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p6051 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6051 : lratChecker f6051 p6051 = .success := by decide +kernel
theorem unsat6051 : Unsatisfiable (PosFin 65) f6051 := by
  apply lratCheckerSound f6051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6051
  · intro a ha; simp [p6051] at ha; subst a; trivial
  · exact checked6051
theorem derived6051 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6051 := by
  apply localUnsat_implies_entails f6051 [c2709, c2820, c2826, c3127] c6051 unsat6051 (by rfl) a
  have h0 : Entails.eval a c2709 := h 2708 (by decide)
  have h1 : Entails.eval a c2820 := h 2819 (by decide)
  have h2 : Entails.eval a c2826 := h 2825 (by decide)
  have h3 : Entails.eval a c3127 := h 3126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6052 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6052 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3418, some c3024, some c3127, some c2904, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6052 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6052 : lratChecker f6052 p6052 = .success := by decide +kernel
theorem unsat6052 : Unsatisfiable (PosFin 65) f6052 := by
  apply lratCheckerSound f6052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6052
  · intro a ha; simp [p6052] at ha; subst a; trivial
  · exact checked6052
theorem derived6052 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6052 := by
  apply localUnsat_implies_entails f6052 [c3418, c3024, c3127, c2904] c6052 unsat6052 (by rfl) a
  have h0 : Entails.eval a c3418 := h 3417 (by decide)
  have h1 : Entails.eval a c3024 := h 3023 (by decide)
  have h2 : Entails.eval a c3127 := h 3126 (by decide)
  have h3 : Entails.eval a c2904 := h 2903 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6053 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨31, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨36, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false), (⟨45, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6053 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2716, some c2813, some c3189, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p6053 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6053 : lratChecker f6053 p6053 = .success := by decide +kernel
theorem unsat6053 : Unsatisfiable (PosFin 65) f6053 := by
  apply lratCheckerSound f6053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6053
  · intro a ha; simp [p6053] at ha; subst a; trivial
  · exact checked6053
theorem derived6053 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6053 := by
  apply localUnsat_implies_entails f6053 [c2716, c2813, c3189] c6053 unsat6053 (by rfl) a
  have h0 : Entails.eval a c2716 := h 2715 (by decide)
  have h1 : Entails.eval a c2813 := h 2812 (by decide)
  have h2 : Entails.eval a c3189 := h 3188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6054 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨46, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6054 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5760, some c5611, some c5635, some c5849, some c5447, some c4079, some c4137, some c3687, some c5964, some c4305, some c4418, some c4559, some c4669, some c4688, some c4821, some c4828, some c4851, some c4760, some c6051, some c6053, some c6052, some c2722, some c2816, some c3189, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6054 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked6054 : lratChecker f6054 p6054 = .success := by decide +kernel
theorem unsat6054 : Unsatisfiable (PosFin 65) f6054 := by
  apply lratCheckerSound f6054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6054
  · intro a ha; simp [p6054] at ha; subst a; trivial
  · exact checked6054
theorem derived6054 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6054 := by
  apply localUnsat_implies_entails f6054 [c5760, c5611, c5635, c5849, c5447, c4079, c4137, c3687, c5964, c4305, c4418, c4559, c4669, c4688, c4821, c4828, c4851, c4760, c6051, c6053, c6052, c2722, c2816, c3189] c6054 unsat6054 (by rfl) a
  have h0 : Entails.eval a c5760 := h 5759 (by decide)
  have h1 : Entails.eval a c5611 := h 5610 (by decide)
  have h2 : Entails.eval a c5635 := h 5634 (by decide)
  have h3 : Entails.eval a c5849 := h 5848 (by decide)
  have h4 : Entails.eval a c5447 := h 5446 (by decide)
  have h5 : Entails.eval a c4079 := h 4078 (by decide)
  have h6 : Entails.eval a c4137 := h 4136 (by decide)
  have h7 : Entails.eval a c3687 := h 3686 (by decide)
  have h8 : Entails.eval a c5964 := derived5964 a h
  have h9 : Entails.eval a c4305 := h 4304 (by decide)
  have h10 : Entails.eval a c4418 := h 4417 (by decide)
  have h11 : Entails.eval a c4559 := h 4558 (by decide)
  have h12 : Entails.eval a c4669 := h 4668 (by decide)
  have h13 : Entails.eval a c4688 := h 4687 (by decide)
  have h14 : Entails.eval a c4821 := h 4820 (by decide)
  have h15 : Entails.eval a c4828 := h 4827 (by decide)
  have h16 : Entails.eval a c4851 := h 4850 (by decide)
  have h17 : Entails.eval a c4760 := h 4759 (by decide)
  have h18 : Entails.eval a c6051 := derived6051 a h
  have h19 : Entails.eval a c6053 := derived6053 a h
  have h20 : Entails.eval a c6052 := derived6052 a h
  have h21 : Entails.eval a c2722 := h 2721 (by decide)
  have h22 : Entails.eval a c2816 := h 2815 (by decide)
  have h23 : Entails.eval a c3189 := h 3188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6055 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨31, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨35, by decide⟩, false), (⟨48, by decide⟩, false), (⟨45, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6055 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2722, some c2816, some c3191, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p6055 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6055 : lratChecker f6055 p6055 = .success := by decide +kernel
theorem unsat6055 : Unsatisfiable (PosFin 65) f6055 := by
  apply lratCheckerSound f6055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6055
  · intro a ha; simp [p6055] at ha; subst a; trivial
  · exact checked6055
theorem derived6055 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6055 := by
  apply localUnsat_implies_entails f6055 [c2722, c2816, c3191] c6055 unsat6055 (by rfl) a
  have h0 : Entails.eval a c2722 := h 2721 (by decide)
  have h1 : Entails.eval a c2816 := h 2815 (by decide)
  have h2 : Entails.eval a c3191 := h 3190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6056 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨31, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6056 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3011, some c3191, some c2828, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p6056 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6056 : lratChecker f6056 p6056 = .success := by decide +kernel
theorem unsat6056 : Unsatisfiable (PosFin 65) f6056 := by
  apply lratCheckerSound f6056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6056
  · intro a ha; simp [p6056] at ha; subst a; trivial
  · exact checked6056
theorem derived6056 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6056 := by
  apply localUnsat_implies_entails f6056 [c3011, c3191, c2828] c6056 unsat6056 (by rfl) a
  have h0 : Entails.eval a c3011 := h 3010 (by decide)
  have h1 : Entails.eval a c3191 := h 3190 (by decide)
  have h2 : Entails.eval a c2828 := h 2827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6057 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6057 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6049, some c6039, some c5999, some c5989, some c6050, some c5760, some c5635, some c5611, some c5849, some c5447, some c4079, some c4418, some c6013, some c4305, some c6015, some c4137, some c3687, some c5964, some c6054, some c4346, some c4904, some c3448, some c4896, some c4000, some c6051, some c6055, some c6056, some c2707, some c2813, some c3127, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6057 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked6057 : lratChecker f6057 p6057 = .success := by decide +kernel
theorem unsat6057 : Unsatisfiable (PosFin 65) f6057 := by
  apply lratCheckerSound f6057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6057
  · intro a ha; simp [p6057] at ha; subst a; trivial
  · exact checked6057
theorem derived6057 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6057 := by
  apply localUnsat_implies_entails f6057 [c6049, c6039, c5999, c5989, c6050, c5760, c5635, c5611, c5849, c5447, c4079, c4418, c6013, c4305, c6015, c4137, c3687, c5964, c6054, c4346, c4904, c3448, c4896, c4000, c6051, c6055, c6056, c2707, c2813, c3127] c6057 unsat6057 (by rfl) a
  have h0 : Entails.eval a c6049 := derived6049 a h
  have h1 : Entails.eval a c6039 := derived6039 a h
  have h2 : Entails.eval a c5999 := derived5999 a h
  have h3 : Entails.eval a c5989 := derived5989 a h
  have h4 : Entails.eval a c6050 := derived6050 a h
  have h5 : Entails.eval a c5760 := h 5759 (by decide)
  have h6 : Entails.eval a c5635 := h 5634 (by decide)
  have h7 : Entails.eval a c5611 := h 5610 (by decide)
  have h8 : Entails.eval a c5849 := h 5848 (by decide)
  have h9 : Entails.eval a c5447 := h 5446 (by decide)
  have h10 : Entails.eval a c4079 := h 4078 (by decide)
  have h11 : Entails.eval a c4418 := h 4417 (by decide)
  have h12 : Entails.eval a c6013 := derived6013 a h
  have h13 : Entails.eval a c4305 := h 4304 (by decide)
  have h14 : Entails.eval a c6015 := derived6015 a h
  have h15 : Entails.eval a c4137 := h 4136 (by decide)
  have h16 : Entails.eval a c3687 := h 3686 (by decide)
  have h17 : Entails.eval a c5964 := derived5964 a h
  have h18 : Entails.eval a c6054 := derived6054 a h
  have h19 : Entails.eval a c4346 := h 4345 (by decide)
  have h20 : Entails.eval a c4904 := h 4903 (by decide)
  have h21 : Entails.eval a c3448 := h 3447 (by decide)
  have h22 : Entails.eval a c4896 := h 4895 (by decide)
  have h23 : Entails.eval a c4000 := h 3999 (by decide)
  have h24 : Entails.eval a c6051 := derived6051 a h
  have h25 : Entails.eval a c6055 := derived6055 a h
  have h26 : Entails.eval a c6056 := derived6056 a h
  have h27 : Entails.eval a c2707 := h 2706 (by decide)
  have h28 : Entails.eval a c2813 := h 2812 (by decide)
  have h29 : Entails.eval a c3127 := h 3126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6058 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨46, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, true), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6058 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5635, some c5611, some c5849, some c5447, some c5412, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6058 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6058 : lratChecker f6058 p6058 = .success := by decide +kernel
theorem unsat6058 : Unsatisfiable (PosFin 65) f6058 := by
  apply lratCheckerSound f6058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6058
  · intro a ha; simp [p6058] at ha; subst a; trivial
  · exact checked6058
theorem derived6058 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6058 := by
  apply localUnsat_implies_entails f6058 [c5635, c5611, c5849, c5447, c5412] c6058 unsat6058 (by rfl) a
  have h0 : Entails.eval a c5635 := h 5634 (by decide)
  have h1 : Entails.eval a c5611 := h 5610 (by decide)
  have h2 : Entails.eval a c5849 := h 5848 (by decide)
  have h3 : Entails.eval a c5447 := h 5446 (by decide)
  have h4 : Entails.eval a c5412 := h 5411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6059 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨46, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6059 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3644, some c3894, some c5447, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6059 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6059 : lratChecker f6059 p6059 = .success := by decide +kernel
theorem unsat6059 : Unsatisfiable (PosFin 65) f6059 := by
  apply lratCheckerSound f6059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6059
  · intro a ha; simp [p6059] at ha; subst a; trivial
  · exact checked6059
theorem derived6059 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6059 := by
  apply localUnsat_implies_entails f6059 [c3644, c3894, c5447] c6059 unsat6059 (by rfl) a
  have h0 : Entails.eval a c3644 := h 3643 (by decide)
  have h1 : Entails.eval a c3894 := h 3893 (by decide)
  have h2 : Entails.eval a c5447 := h 5446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6060 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨45, by decide⟩, true), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨40, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6060 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6058, some c5730, some c5787, some c6059, some c3837, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p6060 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6060 : lratChecker f6060 p6060 = .success := by decide +kernel
theorem unsat6060 : Unsatisfiable (PosFin 65) f6060 := by
  apply lratCheckerSound f6060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6060
  · intro a ha; simp [p6060] at ha; subst a; trivial
  · exact checked6060
theorem derived6060 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6060 := by
  apply localUnsat_implies_entails f6060 [c6058, c5730, c5787, c6059, c3837] c6060 unsat6060 (by rfl) a
  have h0 : Entails.eval a c6058 := derived6058 a h
  have h1 : Entails.eval a c5730 := h 5729 (by decide)
  have h2 : Entails.eval a c5787 := h 5786 (by decide)
  have h3 : Entails.eval a c6059 := derived6059 a h
  have h4 : Entails.eval a c3837 := h 3836 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6061 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6061 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6049, some c6039, some c5999, some c5989, some c6057, some c6060, some c4053, some c3588, some c3463, some c5635, some c5611, some c5849, some c5787, some c3537, some c6040, some c5494, some c5518, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6061 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6061 : lratChecker f6061 p6061 = .success := by decide +kernel
theorem unsat6061 : Unsatisfiable (PosFin 65) f6061 := by
  apply lratCheckerSound f6061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6061
  · intro a ha; simp [p6061] at ha; subst a; trivial
  · exact checked6061
theorem derived6061 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6061 := by
  apply localUnsat_implies_entails f6061 [c6049, c6039, c5999, c5989, c6057, c6060, c4053, c3588, c3463, c5635, c5611, c5849, c5787, c3537, c6040, c5494, c5518] c6061 unsat6061 (by rfl) a
  have h0 : Entails.eval a c6049 := derived6049 a h
  have h1 : Entails.eval a c6039 := derived6039 a h
  have h2 : Entails.eval a c5999 := derived5999 a h
  have h3 : Entails.eval a c5989 := derived5989 a h
  have h4 : Entails.eval a c6057 := derived6057 a h
  have h5 : Entails.eval a c6060 := derived6060 a h
  have h6 : Entails.eval a c4053 := h 4052 (by decide)
  have h7 : Entails.eval a c3588 := h 3587 (by decide)
  have h8 : Entails.eval a c3463 := h 3462 (by decide)
  have h9 : Entails.eval a c5635 := h 5634 (by decide)
  have h10 : Entails.eval a c5611 := h 5610 (by decide)
  have h11 : Entails.eval a c5849 := h 5848 (by decide)
  have h12 : Entails.eval a c5787 := h 5786 (by decide)
  have h13 : Entails.eval a c3537 := h 3536 (by decide)
  have h14 : Entails.eval a c6040 := derived6040 a h
  have h15 : Entails.eval a c5494 := h 5493 (by decide)
  have h16 : Entails.eval a c5518 := h 5517 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6062 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨64, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6062 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4062, some c3597, some c6043, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6062 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6062 : lratChecker f6062 p6062 = .success := by decide +kernel
theorem unsat6062 : Unsatisfiable (PosFin 65) f6062 := by
  apply lratCheckerSound f6062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6062
  · intro a ha; simp [p6062] at ha; subst a; trivial
  · exact checked6062
theorem derived6062 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6062 := by
  apply localUnsat_implies_entails f6062 [c4062, c3597, c6043] c6062 unsat6062 (by rfl) a
  have h0 : Entails.eval a c4062 := h 4061 (by decide)
  have h1 : Entails.eval a c3597 := h 3596 (by decide)
  have h2 : Entails.eval a c6043 := derived6043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6063 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6063 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6061, some c6049, some c6039, some c5999, some c5989, some c6043, some c6025, some c3944, some c3550, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6063 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6063 : lratChecker f6063 p6063 = .success := by decide +kernel
theorem unsat6063 : Unsatisfiable (PosFin 65) f6063 := by
  apply lratCheckerSound f6063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6063
  · intro a ha; simp [p6063] at ha; subst a; trivial
  · exact checked6063
theorem derived6063 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6063 := by
  apply localUnsat_implies_entails f6063 [c6061, c6049, c6039, c5999, c5989, c6043, c6025, c3944, c3550] c6063 unsat6063 (by rfl) a
  have h0 : Entails.eval a c6061 := derived6061 a h
  have h1 : Entails.eval a c6049 := derived6049 a h
  have h2 : Entails.eval a c6039 := derived6039 a h
  have h3 : Entails.eval a c5999 := derived5999 a h
  have h4 : Entails.eval a c5989 := derived5989 a h
  have h5 : Entails.eval a c6043 := derived6043 a h
  have h6 : Entails.eval a c6025 := derived6025 a h
  have h7 : Entails.eval a c3944 := h 3943 (by decide)
  have h8 : Entails.eval a c3550 := h 3549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6064 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6064 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4309, some c5445, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6064 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6064 : lratChecker f6064 p6064 = .success := by decide +kernel
theorem unsat6064 : Unsatisfiable (PosFin 65) f6064 := by
  apply lratCheckerSound f6064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6064
  · intro a ha; simp [p6064] at ha; subst a; trivial
  · exact checked6064
theorem derived6064 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6064 := by
  apply localUnsat_implies_entails f6064 [c4309, c5445] c6064 unsat6064 (by rfl) a
  have h0 : Entails.eval a c4309 := h 4308 (by decide)
  have h1 : Entails.eval a c5445 := h 5444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6065 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6065 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6063, some c6061, some c6039, some c6062, some c5999, some c5989, some c5390, some c4031, some c4658, some c4349, some c4393, some c6064, some c3619, some c4414, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6065 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6065 : lratChecker f6065 p6065 = .success := by decide +kernel
theorem unsat6065 : Unsatisfiable (PosFin 65) f6065 := by
  apply lratCheckerSound f6065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6065
  · intro a ha; simp [p6065] at ha; subst a; trivial
  · exact checked6065
theorem derived6065 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6065 := by
  apply localUnsat_implies_entails f6065 [c6063, c6061, c6039, c6062, c5999, c5989, c5390, c4031, c4658, c4349, c4393, c6064, c3619, c4414] c6065 unsat6065 (by rfl) a
  have h0 : Entails.eval a c6063 := derived6063 a h
  have h1 : Entails.eval a c6061 := derived6061 a h
  have h2 : Entails.eval a c6039 := derived6039 a h
  have h3 : Entails.eval a c6062 := derived6062 a h
  have h4 : Entails.eval a c5999 := derived5999 a h
  have h5 : Entails.eval a c5989 := derived5989 a h
  have h6 : Entails.eval a c5390 := h 5389 (by decide)
  have h7 : Entails.eval a c4031 := h 4030 (by decide)
  have h8 : Entails.eval a c4658 := h 4657 (by decide)
  have h9 : Entails.eval a c4349 := h 4348 (by decide)
  have h10 : Entails.eval a c4393 := h 4392 (by decide)
  have h11 : Entails.eval a c6064 := derived6064 a h
  have h12 : Entails.eval a c3619 := h 3618 (by decide)
  have h13 : Entails.eval a c4414 := h 4413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6066 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6066 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6039, some c6061, some c6062, some c6063, some c6065, some c3652, some c5763, some c4888, some c4703, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6066 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6066 : lratChecker f6066 p6066 = .success := by decide +kernel
theorem unsat6066 : Unsatisfiable (PosFin 65) f6066 := by
  apply lratCheckerSound f6066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6066
  · intro a ha; simp [p6066] at ha; subst a; trivial
  · exact checked6066
theorem derived6066 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6066 := by
  apply localUnsat_implies_entails f6066 [c6039, c6061, c6062, c6063, c6065, c3652, c5763, c4888, c4703] c6066 unsat6066 (by rfl) a
  have h0 : Entails.eval a c6039 := derived6039 a h
  have h1 : Entails.eval a c6061 := derived6061 a h
  have h2 : Entails.eval a c6062 := derived6062 a h
  have h3 : Entails.eval a c6063 := derived6063 a h
  have h4 : Entails.eval a c6065 := derived6065 a h
  have h5 : Entails.eval a c3652 := h 3651 (by decide)
  have h6 : Entails.eval a c5763 := h 5762 (by decide)
  have h7 : Entails.eval a c4888 := h 4887 (by decide)
  have h8 : Entails.eval a c4703 := h 4702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6067 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨37, by decide⟩, true), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6067 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6062, some c6048, some c5763, some c4888, some c4807, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6067 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6067 : lratChecker f6067 p6067 = .success := by decide +kernel
theorem unsat6067 : Unsatisfiable (PosFin 65) f6067 := by
  apply lratCheckerSound f6067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6067
  · intro a ha; simp [p6067] at ha; subst a; trivial
  · exact checked6067
theorem derived6067 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6067 := by
  apply localUnsat_implies_entails f6067 [c6062, c6048, c5763, c4888, c4807] c6067 unsat6067 (by rfl) a
  have h0 : Entails.eval a c6062 := derived6062 a h
  have h1 : Entails.eval a c6048 := derived6048 a h
  have h2 : Entails.eval a c5763 := h 5762 (by decide)
  have h3 : Entails.eval a c4888 := h 4887 (by decide)
  have h4 : Entails.eval a c4807 := h 4806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6068 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨42, by decide⟩, true), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨45, by decide⟩, true), (⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6068 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6064, some c3619, some c3893, some c5662, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6068 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6068 : lratChecker f6068 p6068 = .success := by decide +kernel
theorem unsat6068 : Unsatisfiable (PosFin 65) f6068 := by
  apply lratCheckerSound f6068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6068
  · intro a ha; simp [p6068] at ha; subst a; trivial
  · exact checked6068
theorem derived6068 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6068 := by
  apply localUnsat_implies_entails f6068 [c6064, c3619, c3893, c5662] c6068 unsat6068 (by rfl) a
  have h0 : Entails.eval a c6064 := derived6064 a h
  have h1 : Entails.eval a c3619 := h 3618 (by decide)
  have h2 : Entails.eval a c3893 := h 3892 (by decide)
  have h3 : Entails.eval a c5662 := h 5661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6069 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨60, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6069 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5947, some c4411, some c4543, some c3630, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6069 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6069 : lratChecker f6069 p6069 = .success := by decide +kernel
theorem unsat6069 : Unsatisfiable (PosFin 65) f6069 := by
  apply lratCheckerSound f6069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6069
  · intro a ha; simp [p6069] at ha; subst a; trivial
  · exact checked6069
theorem derived6069 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6069 := by
  apply localUnsat_implies_entails f6069 [c5947, c4411, c4543, c3630] c6069 unsat6069 (by rfl) a
  have h0 : Entails.eval a c5947 := derived5947 a h
  have h1 : Entails.eval a c4411 := h 4410 (by decide)
  have h2 : Entails.eval a c4543 := h 4542 (by decide)
  have h3 : Entails.eval a c3630 := h 3629 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6070 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨41, by decide⟩, true), (⟨44, by decide⟩, false), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨34, by decide⟩, false), (⟨42, by decide⟩, true), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨45, by decide⟩, true), (⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6070 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6068, some c6069, some c4312, some c4309, some c5820, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6070 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6070 : lratChecker f6070 p6070 = .success := by decide +kernel
theorem unsat6070 : Unsatisfiable (PosFin 65) f6070 := by
  apply lratCheckerSound f6070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6070
  · intro a ha; simp [p6070] at ha; subst a; trivial
  · exact checked6070
theorem derived6070 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6070 := by
  apply localUnsat_implies_entails f6070 [c6068, c6069, c4312, c4309, c5820] c6070 unsat6070 (by rfl) a
  have h0 : Entails.eval a c6068 := derived6068 a h
  have h1 : Entails.eval a c6069 := derived6069 a h
  have h2 : Entails.eval a c4312 := h 4311 (by decide)
  have h3 : Entails.eval a c4309 := h 4308 (by decide)
  have h4 : Entails.eval a c5820 := h 5819 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6071 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6071 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3421, some c3130, some c2704, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6071 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6071 : lratChecker f6071 p6071 = .success := by decide +kernel
theorem unsat6071 : Unsatisfiable (PosFin 65) f6071 := by
  apply lratCheckerSound f6071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6071
  · intro a ha; simp [p6071] at ha; subst a; trivial
  · exact checked6071
theorem derived6071 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6071 := by
  apply localUnsat_implies_entails f6071 [c3421, c3130, c2704] c6071 unsat6071 (by rfl) a
  have h0 : Entails.eval a c3421 := h 3420 (by decide)
  have h1 : Entails.eval a c3130 := h 3129 (by decide)
  have h2 : Entails.eval a c2704 := h 2703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6072 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6072 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2730, some c3398, some c3400, some c3231, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6072 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6072 : lratChecker f6072 p6072 = .success := by decide +kernel
theorem unsat6072 : Unsatisfiable (PosFin 65) f6072 := by
  apply lratCheckerSound f6072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6072
  · intro a ha; simp [p6072] at ha; subst a; trivial
  · exact checked6072
theorem derived6072 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6072 := by
  apply localUnsat_implies_entails f6072 [c2730, c3398, c3400, c3231] c6072 unsat6072 (by rfl) a
  have h0 : Entails.eval a c2730 := h 2729 (by decide)
  have h1 : Entails.eval a c3398 := h 3397 (by decide)
  have h2 : Entails.eval a c3400 := h 3399 (by decide)
  have h3 : Entails.eval a c3231 := h 3230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6073 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨60, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, false), (⟨43, by decide⟩, false), (⟨36, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6073 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2738, some c2774, some c2804, some c3220, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6073 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6073 : lratChecker f6073 p6073 = .success := by decide +kernel
theorem unsat6073 : Unsatisfiable (PosFin 65) f6073 := by
  apply lratCheckerSound f6073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6073
  · intro a ha; simp [p6073] at ha; subst a; trivial
  · exact checked6073
theorem derived6073 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6073 := by
  apply localUnsat_implies_entails f6073 [c2738, c2774, c2804, c3220] c6073 unsat6073 (by rfl) a
  have h0 : Entails.eval a c2738 := h 2737 (by decide)
  have h1 : Entails.eval a c2774 := h 2773 (by decide)
  have h2 : Entails.eval a c2804 := h 2803 (by decide)
  have h3 : Entails.eval a c3220 := h 3219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6074 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨60, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6074 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6066, some c4312, some c4309, some c4302, some c5583, some c5577, some c5458, some c6073, some c6071, some c2730, some c2758, some c6072, some c3208, some c3153, some c2938, some c2915, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6074 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked6074 : lratChecker f6074 p6074 = .success := by decide +kernel
theorem unsat6074 : Unsatisfiable (PosFin 65) f6074 := by
  apply lratCheckerSound f6074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6074
  · intro a ha; simp [p6074] at ha; subst a; trivial
  · exact checked6074
theorem derived6074 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6074 := by
  apply localUnsat_implies_entails f6074 [c6066, c4312, c4309, c4302, c5583, c5577, c5458, c6073, c6071, c2730, c2758, c6072, c3208, c3153, c2938, c2915] c6074 unsat6074 (by rfl) a
  have h0 : Entails.eval a c6066 := derived6066 a h
  have h1 : Entails.eval a c4312 := h 4311 (by decide)
  have h2 : Entails.eval a c4309 := h 4308 (by decide)
  have h3 : Entails.eval a c4302 := h 4301 (by decide)
  have h4 : Entails.eval a c5583 := h 5582 (by decide)
  have h5 : Entails.eval a c5577 := h 5576 (by decide)
  have h6 : Entails.eval a c5458 := h 5457 (by decide)
  have h7 : Entails.eval a c6073 := derived6073 a h
  have h8 : Entails.eval a c6071 := derived6071 a h
  have h9 : Entails.eval a c2730 := h 2729 (by decide)
  have h10 : Entails.eval a c2758 := h 2757 (by decide)
  have h11 : Entails.eval a c6072 := derived6072 a h
  have h12 : Entails.eval a c3208 := h 3207 (by decide)
  have h13 : Entails.eval a c3153 := h 3152 (by decide)
  have h14 : Entails.eval a c2938 := h 2937 (by decide)
  have h15 : Entails.eval a c2915 := h 2914 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6075 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6075 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6062, some c6067, some c3652, some c5336, some c3778, some c3708, some c5390, some c4658, some c4349, some c4393, some c5793, some c4031, some c6066, some c6074, some c3735, some c4411, some c5663, some c3730, some c5655, some c3635, some c6073, some c6071, some c2730, some c2758, some c6072, some c3208, some c3153, some c2938, some c2915, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6075 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked6075 : lratChecker f6075 p6075 = .success := by decide +kernel
theorem unsat6075 : Unsatisfiable (PosFin 65) f6075 := by
  apply lratCheckerSound f6075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6075
  · intro a ha; simp [p6075] at ha; subst a; trivial
  · exact checked6075
theorem derived6075 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6075 := by
  apply localUnsat_implies_entails f6075 [c6062, c6067, c3652, c5336, c3778, c3708, c5390, c4658, c4349, c4393, c5793, c4031, c6066, c6074, c3735, c4411, c5663, c3730, c5655, c3635, c6073, c6071, c2730, c2758, c6072, c3208, c3153, c2938, c2915] c6075 unsat6075 (by rfl) a
  have h0 : Entails.eval a c6062 := derived6062 a h
  have h1 : Entails.eval a c6067 := derived6067 a h
  have h2 : Entails.eval a c3652 := h 3651 (by decide)
  have h3 : Entails.eval a c5336 := h 5335 (by decide)
  have h4 : Entails.eval a c3778 := h 3777 (by decide)
  have h5 : Entails.eval a c3708 := h 3707 (by decide)
  have h6 : Entails.eval a c5390 := h 5389 (by decide)
  have h7 : Entails.eval a c4658 := h 4657 (by decide)
  have h8 : Entails.eval a c4349 := h 4348 (by decide)
  have h9 : Entails.eval a c4393 := h 4392 (by decide)
  have h10 : Entails.eval a c5793 := h 5792 (by decide)
  have h11 : Entails.eval a c4031 := h 4030 (by decide)
  have h12 : Entails.eval a c6066 := derived6066 a h
  have h13 : Entails.eval a c6074 := derived6074 a h
  have h14 : Entails.eval a c3735 := h 3734 (by decide)
  have h15 : Entails.eval a c4411 := h 4410 (by decide)
  have h16 : Entails.eval a c5663 := h 5662 (by decide)
  have h17 : Entails.eval a c3730 := h 3729 (by decide)
  have h18 : Entails.eval a c5655 := h 5654 (by decide)
  have h19 : Entails.eval a c3635 := h 3634 (by decide)
  have h20 : Entails.eval a c6073 := derived6073 a h
  have h21 : Entails.eval a c6071 := derived6071 a h
  have h22 : Entails.eval a c2730 := h 2729 (by decide)
  have h23 : Entails.eval a c2758 := h 2757 (by decide)
  have h24 : Entails.eval a c6072 := derived6072 a h
  have h25 : Entails.eval a c3208 := h 3207 (by decide)
  have h26 : Entails.eval a c3153 := h 3152 (by decide)
  have h27 : Entails.eval a c2938 := h 2937 (by decide)
  have h28 : Entails.eval a c2915 := h 2914 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6076 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨60, by decide⟩, true), (⟨52, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6076 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3735, some c5663, some c5604, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6076 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6076 : lratChecker f6076 p6076 = .success := by decide +kernel
theorem unsat6076 : Unsatisfiable (PosFin 65) f6076 := by
  apply lratCheckerSound f6076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6076
  · intro a ha; simp [p6076] at ha; subst a; trivial
  · exact checked6076
theorem derived6076 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6076 := by
  apply localUnsat_implies_entails f6076 [c3735, c5663, c5604] c6076 unsat6076 (by rfl) a
  have h0 : Entails.eval a c3735 := h 3734 (by decide)
  have h1 : Entails.eval a c5663 := h 5662 (by decide)
  have h2 : Entails.eval a c5604 := h 5603 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6077 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6077 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6062, some c6067, some c3652, some c5390, some c4658, some c4349, some c4393, some c5793, some c4031, some c5336, some c6070, some c6075, some c6076, some c4309, some c4916, some c4302, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6077 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked6077 : lratChecker f6077 p6077 = .success := by decide +kernel
theorem unsat6077 : Unsatisfiable (PosFin 65) f6077 := by
  apply lratCheckerSound f6077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6077
  · intro a ha; simp [p6077] at ha; subst a; trivial
  · exact checked6077
theorem derived6077 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6077 := by
  apply localUnsat_implies_entails f6077 [c6062, c6067, c3652, c5390, c4658, c4349, c4393, c5793, c4031, c5336, c6070, c6075, c6076, c4309, c4916, c4302] c6077 unsat6077 (by rfl) a
  have h0 : Entails.eval a c6062 := derived6062 a h
  have h1 : Entails.eval a c6067 := derived6067 a h
  have h2 : Entails.eval a c3652 := h 3651 (by decide)
  have h3 : Entails.eval a c5390 := h 5389 (by decide)
  have h4 : Entails.eval a c4658 := h 4657 (by decide)
  have h5 : Entails.eval a c4349 := h 4348 (by decide)
  have h6 : Entails.eval a c4393 := h 4392 (by decide)
  have h7 : Entails.eval a c5793 := h 5792 (by decide)
  have h8 : Entails.eval a c4031 := h 4030 (by decide)
  have h9 : Entails.eval a c5336 := h 5335 (by decide)
  have h10 : Entails.eval a c6070 := derived6070 a h
  have h11 : Entails.eval a c6075 := derived6075 a h
  have h12 : Entails.eval a c6076 := derived6076 a h
  have h13 : Entails.eval a c4309 := h 4308 (by decide)
  have h14 : Entails.eval a c4916 := h 4915 (by decide)
  have h15 : Entails.eval a c4302 := h 4301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6078 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨41, by decide⟩, false), (⟨34, by decide⟩, false), (⟨45, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6078 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3708, some c4118, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6078 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6078 : lratChecker f6078 p6078 = .success := by decide +kernel
theorem unsat6078 : Unsatisfiable (PosFin 65) f6078 := by
  apply lratCheckerSound f6078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6078
  · intro a ha; simp [p6078] at ha; subst a; trivial
  · exact checked6078
theorem derived6078 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6078 := by
  apply localUnsat_implies_entails f6078 [c3708, c4118] c6078 unsat6078 (by rfl) a
  have h0 : Entails.eval a c3708 := h 3707 (by decide)
  have h1 : Entails.eval a c4118 := h 4117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6079 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6079 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6062, some c6067, some c3652, some c5336, some c5390, some c4031, some c4658, some c4349, some c4393, some c6077, some c6018, some c6078, some c6068, some c6008, some c4129, some c4472, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6079 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked6079 : lratChecker f6079 p6079 = .success := by decide +kernel
theorem unsat6079 : Unsatisfiable (PosFin 65) f6079 := by
  apply lratCheckerSound f6079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6079
  · intro a ha; simp [p6079] at ha; subst a; trivial
  · exact checked6079
theorem derived6079 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6079 := by
  apply localUnsat_implies_entails f6079 [c6062, c6067, c3652, c5336, c5390, c4031, c4658, c4349, c4393, c6077, c6018, c6078, c6068, c6008, c4129, c4472] c6079 unsat6079 (by rfl) a
  have h0 : Entails.eval a c6062 := derived6062 a h
  have h1 : Entails.eval a c6067 := derived6067 a h
  have h2 : Entails.eval a c3652 := h 3651 (by decide)
  have h3 : Entails.eval a c5336 := h 5335 (by decide)
  have h4 : Entails.eval a c5390 := h 5389 (by decide)
  have h5 : Entails.eval a c4031 := h 4030 (by decide)
  have h6 : Entails.eval a c4658 := h 4657 (by decide)
  have h7 : Entails.eval a c4349 := h 4348 (by decide)
  have h8 : Entails.eval a c4393 := h 4392 (by decide)
  have h9 : Entails.eval a c6077 := derived6077 a h
  have h10 : Entails.eval a c6018 := derived6018 a h
  have h11 : Entails.eval a c6078 := derived6078 a h
  have h12 : Entails.eval a c6068 := derived6068 a h
  have h13 : Entails.eval a c6008 := derived6008 a h
  have h14 : Entails.eval a c4129 := h 4128 (by decide)
  have h15 : Entails.eval a c4472 := h 4471 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6080 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6080 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3714, some c3697, some c3687, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6080 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6080 : lratChecker f6080 p6080 = .success := by decide +kernel
theorem unsat6080 : Unsatisfiable (PosFin 65) f6080 := by
  apply lratCheckerSound f6080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6080
  · intro a ha; simp [p6080] at ha; subst a; trivial
  · exact checked6080
theorem derived6080 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6080 := by
  apply localUnsat_implies_entails f6080 [c3714, c3697, c3687] c6080 unsat6080 (by rfl) a
  have h0 : Entails.eval a c3714 := h 3713 (by decide)
  have h1 : Entails.eval a c3697 := h 3696 (by decide)
  have h2 : Entails.eval a c3687 := h 3686 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived6080

end CochromaticTwenty.Certificates.FixedCore1
