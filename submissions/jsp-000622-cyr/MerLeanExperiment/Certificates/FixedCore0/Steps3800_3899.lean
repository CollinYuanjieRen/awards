import MerLeanExperiment.Certificates.FixedCore0.Steps3700_3799

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c11351 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨21, by decide⟩, false), (⟨59, by decide⟩, true), (⟨51, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11351 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11345, some c11346, some c11348, some c11349, some c11302, some c4054, some c11350, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11351 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11351 : lratChecker f11351 p11351 = .success := by decide +kernel
theorem unsat11351 : Unsatisfiable (PosFin 65) f11351 := by
  apply lratCheckerSound f11351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11351
  · intro a ha; simp [p11351] at ha; subst a; trivial
  · exact checked11351
theorem derived11351 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11351 := by
  apply localUnsat_implies_entails f11351 [c11170, c11345, c11346, c11348, c11349, c11302, c4054, c11350] c11351 unsat11351 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11345 := derived11345 a h
  have h2 : Entails.eval a c11346 := derived11346 a h
  have h3 : Entails.eval a c11348 := derived11348 a h
  have h4 : Entails.eval a c11349 := derived11349 a h
  have h5 : Entails.eval a c11302 := derived11302 a h
  have h6 : Entails.eval a c4054 := h 4053 (by decide)
  have h7 : Entails.eval a c11350 := derived11350 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11352 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨51, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11352 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11256, some c11170, some c8269, some c4084, some c4082, some c4077, some c4092, some c4086, some c5000, some c4093, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11352 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11352 : lratChecker f11352 p11352 = .success := by decide +kernel
theorem unsat11352 : Unsatisfiable (PosFin 65) f11352 := by
  apply lratCheckerSound f11352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11352
  · intro a ha; simp [p11352] at ha; subst a; trivial
  · exact checked11352
theorem derived11352 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11352 := by
  apply localUnsat_implies_entails f11352 [c11018, c11256, c11170, c8269, c4084, c4082, c4077, c4092, c4086, c5000, c4093] c11352 unsat11352 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c4084 := h 4083 (by decide)
  have h5 : Entails.eval a c4082 := h 4081 (by decide)
  have h6 : Entails.eval a c4077 := h 4076 (by decide)
  have h7 : Entails.eval a c4092 := h 4091 (by decide)
  have h8 : Entails.eval a c4086 := h 4085 (by decide)
  have h9 : Entails.eval a c5000 := h 4999 (by decide)
  have h10 : Entails.eval a c4093 := h 4092 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11353 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨59, by decide⟩, true), (⟨51, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11353 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11256, some c11170, some c11345, some c11351, some c8007, some c11352, some c10306, some c11210, some c10764, some c10339, some c2793, some c10790, some c10769, some c3688, some c339, some c2542, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11353 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11353 : lratChecker f11353 p11353 = .success := by decide +kernel
theorem unsat11353 : Unsatisfiable (PosFin 65) f11353 := by
  apply lratCheckerSound f11353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11353
  · intro a ha; simp [p11353] at ha; subst a; trivial
  · exact checked11353
theorem derived11353 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11353 := by
  apply localUnsat_implies_entails f11353 [c11331, c11256, c11170, c11345, c11351, c8007, c11352, c10306, c11210, c10764, c10339, c2793, c10790, c10769, c3688, c339, c2542] c11353 unsat11353 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11345 := derived11345 a h
  have h4 : Entails.eval a c11351 := derived11351 a h
  have h5 : Entails.eval a c8007 := derived8007 a h
  have h6 : Entails.eval a c11352 := derived11352 a h
  have h7 : Entails.eval a c10306 := derived10306 a h
  have h8 : Entails.eval a c11210 := derived11210 a h
  have h9 : Entails.eval a c10764 := derived10764 a h
  have h10 : Entails.eval a c10339 := derived10339 a h
  have h11 : Entails.eval a c2793 := h 2792 (by decide)
  have h12 : Entails.eval a c10790 := derived10790 a h
  have h13 : Entails.eval a c10769 := derived10769 a h
  have h14 : Entails.eval a c3688 := h 3687 (by decide)
  have h15 : Entails.eval a c339 := h 338 (by decide)
  have h16 : Entails.eval a c2542 := h 2541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11354 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11354 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11210, some c10777, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11354 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11354 : lratChecker f11354 p11354 = .success := by decide +kernel
theorem unsat11354 : Unsatisfiable (PosFin 65) f11354 := by
  apply lratCheckerSound f11354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11354
  · intro a ha; simp [p11354] at ha; subst a; trivial
  · exact checked11354
theorem derived11354 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11354 := by
  apply localUnsat_implies_entails f11354 [c11210, c10777] c11354 unsat11354 (by rfl) a
  have h0 : Entails.eval a c11210 := derived11210 a h
  have h1 : Entails.eval a c10777 := derived10777 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11355 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨51, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11355 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11345, some c11353, some c11354, some c11352, some c11346, some c11302, some c11350, some c4054, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11355 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11355 : lratChecker f11355 p11355 = .success := by decide +kernel
theorem unsat11355 : Unsatisfiable (PosFin 65) f11355 := by
  apply lratCheckerSound f11355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11355
  · intro a ha; simp [p11355] at ha; subst a; trivial
  · exact checked11355
theorem derived11355 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11355 := by
  apply localUnsat_implies_entails f11355 [c11170, c11345, c11353, c11354, c11352, c11346, c11302, c11350, c4054] c11355 unsat11355 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11345 := derived11345 a h
  have h2 : Entails.eval a c11353 := derived11353 a h
  have h3 : Entails.eval a c11354 := derived11354 a h
  have h4 : Entails.eval a c11352 := derived11352 a h
  have h5 : Entails.eval a c11346 := derived11346 a h
  have h6 : Entails.eval a c11302 := derived11302 a h
  have h7 : Entails.eval a c11350 := derived11350 a h
  have h8 : Entails.eval a c4054 := h 4053 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11356 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨59, by decide⟩, false), (⟨51, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11356 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11051, some c4089, some c4073, some c4998, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11356 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11356 : lratChecker f11356 p11356 = .success := by decide +kernel
theorem unsat11356 : Unsatisfiable (PosFin 65) f11356 := by
  apply lratCheckerSound f11356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11356
  · intro a ha; simp [p11356] at ha; subst a; trivial
  · exact checked11356
theorem derived11356 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11356 := by
  apply localUnsat_implies_entails f11356 [c11170, c11256, c11051, c4089, c4073, c4998] c11356 unsat11356 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11051 := derived11051 a h
  have h3 : Entails.eval a c4089 := h 4088 (by decide)
  have h4 : Entails.eval a c4073 := h 4072 (by decide)
  have h5 : Entails.eval a c4998 := h 4997 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11357 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11357 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11018, some c11170, some c11345, some c11355, some c11051, some c11356, some c11210, some c10764, some c11354, some c10321, some c10790, some c10766, some c10341, some c10309, some c10684, some c334, some c10314, some c335, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11357 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked11357 : lratChecker f11357 p11357 = .success := by decide +kernel
theorem unsat11357 : Unsatisfiable (PosFin 65) f11357 := by
  apply lratCheckerSound f11357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11357
  · intro a ha; simp [p11357] at ha; subst a; trivial
  · exact checked11357
theorem derived11357 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11357 := by
  apply localUnsat_implies_entails f11357 [c11331, c11018, c11170, c11345, c11355, c11051, c11356, c11210, c10764, c11354, c10321, c10790, c10766, c10341, c10309, c10684, c334, c10314, c335] c11357 unsat11357 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11018 := derived11018 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11345 := derived11345 a h
  have h4 : Entails.eval a c11355 := derived11355 a h
  have h5 : Entails.eval a c11051 := derived11051 a h
  have h6 : Entails.eval a c11356 := derived11356 a h
  have h7 : Entails.eval a c11210 := derived11210 a h
  have h8 : Entails.eval a c10764 := derived10764 a h
  have h9 : Entails.eval a c11354 := derived11354 a h
  have h10 : Entails.eval a c10321 := derived10321 a h
  have h11 : Entails.eval a c10790 := derived10790 a h
  have h12 : Entails.eval a c10766 := derived10766 a h
  have h13 : Entails.eval a c10341 := derived10341 a h
  have h14 : Entails.eval a c10309 := derived10309 a h
  have h15 : Entails.eval a c10684 := derived10684 a h
  have h16 : Entails.eval a c334 := h 333 (by decide)
  have h17 : Entails.eval a c10314 := derived10314 a h
  have h18 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11358 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨51, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11358 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10343, some c10342, some c10320, some c10330, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11358 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11358 : lratChecker f11358 p11358 = .success := by decide +kernel
theorem unsat11358 : Unsatisfiable (PosFin 65) f11358 := by
  apply lratCheckerSound f11358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11358
  · intro a ha; simp [p11358] at ha; subst a; trivial
  · exact checked11358
theorem derived11358 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11358 := by
  apply localUnsat_implies_entails f11358 [c11018, c10343, c10342, c10320, c10330] c11358 unsat11358 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10343 := derived10343 a h
  have h2 : Entails.eval a c10342 := derived10342 a h
  have h3 : Entails.eval a c10320 := derived10320 a h
  have h4 : Entails.eval a c10330 := derived10330 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11359 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11359 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11345, some c11358, some c4079, some c11050, some c4091, some c4083, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11359 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11359 : lratChecker f11359 p11359 = .success := by decide +kernel
theorem unsat11359 : Unsatisfiable (PosFin 65) f11359 := by
  apply lratCheckerSound f11359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11359
  · intro a ha; simp [p11359] at ha; subst a; trivial
  · exact checked11359
theorem derived11359 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11359 := by
  apply localUnsat_implies_entails f11359 [c11018, c11170, c11345, c11358, c4079, c11050, c4091, c4083] c11359 unsat11359 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11345 := derived11345 a h
  have h3 : Entails.eval a c11358 := derived11358 a h
  have h4 : Entails.eval a c4079 := h 4078 (by decide)
  have h5 : Entails.eval a c11050 := derived11050 a h
  have h6 : Entails.eval a c4091 := h 4090 (by decide)
  have h7 : Entails.eval a c4083 := h 4082 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11360 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11360 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11170, some c11359, some c11345, some c11356, some c11352, some c11302, some c4976, some c4978, some c4979, some c4062, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11360 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11360 : lratChecker f11360 p11360 = .success := by decide +kernel
theorem unsat11360 : Unsatisfiable (PosFin 65) f11360 := by
  apply lratCheckerSound f11360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11360
  · intro a ha; simp [p11360] at ha; subst a; trivial
  · exact checked11360
theorem derived11360 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11360 := by
  apply localUnsat_implies_entails f11360 [c11256, c11170, c11359, c11345, c11356, c11352, c11302, c4976, c4978, c4979, c4062] c11360 unsat11360 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11359 := derived11359 a h
  have h3 : Entails.eval a c11345 := derived11345 a h
  have h4 : Entails.eval a c11356 := derived11356 a h
  have h5 : Entails.eval a c11352 := derived11352 a h
  have h6 : Entails.eval a c11302 := derived11302 a h
  have h7 : Entails.eval a c4976 := h 4975 (by decide)
  have h8 : Entails.eval a c4978 := h 4977 (by decide)
  have h9 : Entails.eval a c4979 := h 4978 (by decide)
  have h10 : Entails.eval a c4062 := h 4061 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11361 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11361 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11360, some c10514, some c10421, some c10481, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11361 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11361 : lratChecker f11361 p11361 = .success := by decide +kernel
theorem unsat11361 : Unsatisfiable (PosFin 65) f11361 := by
  apply lratCheckerSound f11361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11361
  · intro a ha; simp [p11361] at ha; subst a; trivial
  · exact checked11361
theorem derived11361 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11361 := by
  apply localUnsat_implies_entails f11361 [c11331, c11360, c10514, c10421, c10481] c11361 unsat11361 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11360 := derived11360 a h
  have h2 : Entails.eval a c10514 := derived10514 a h
  have h3 : Entails.eval a c10421 := derived10421 a h
  have h4 : Entails.eval a c10481 := derived10481 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11362 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11362 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10336, some c10324, some c10746, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11362 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11362 : lratChecker f11362 p11362 = .success := by decide +kernel
theorem unsat11362 : Unsatisfiable (PosFin 65) f11362 := by
  apply lratCheckerSound f11362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11362
  · intro a ha; simp [p11362] at ha; subst a; trivial
  · exact checked11362
theorem derived11362 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11362 := by
  apply localUnsat_implies_entails f11362 [c11331, c10336, c10324, c10746] c11362 unsat11362 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10336 := derived10336 a h
  have h2 : Entails.eval a c10324 := derived10324 a h
  have h3 : Entails.eval a c10746 := derived10746 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11363 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨18, by decide⟩, true), (⟨28, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11363 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10503, some c10808, some c10486, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p11363 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11363 : lratChecker f11363 p11363 = .success := by decide +kernel
theorem unsat11363 : Unsatisfiable (PosFin 65) f11363 := by
  apply lratCheckerSound f11363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11363
  · intro a ha; simp [p11363] at ha; subst a; trivial
  · exact checked11363
theorem derived11363 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11363 := by
  apply localUnsat_implies_entails f11363 [c11331, c10503, c10808, c10486] c11363 unsat11363 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10503 := derived10503 a h
  have h2 : Entails.eval a c10808 := derived10808 a h
  have h3 : Entails.eval a c10486 := derived10486 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11364 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨28, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11364 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11018, some c11357, some c11360, some c11361, some c10771, some c11363, some c10398, some c10689, some c11362, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p11364 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11364 : lratChecker f11364 p11364 = .success := by decide +kernel
theorem unsat11364 : Unsatisfiable (PosFin 65) f11364 := by
  apply lratCheckerSound f11364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11364
  · intro a ha; simp [p11364] at ha; subst a; trivial
  · exact checked11364
theorem derived11364 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11364 := by
  apply localUnsat_implies_entails f11364 [c11331, c11018, c11357, c11360, c11361, c10771, c11363, c10398, c10689, c11362] c11364 unsat11364 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11018 := derived11018 a h
  have h2 : Entails.eval a c11357 := derived11357 a h
  have h3 : Entails.eval a c11360 := derived11360 a h
  have h4 : Entails.eval a c11361 := derived11361 a h
  have h5 : Entails.eval a c10771 := derived10771 a h
  have h6 : Entails.eval a c11363 := derived11363 a h
  have h7 : Entails.eval a c10398 := derived10398 a h
  have h8 : Entails.eval a c10689 := derived10689 a h
  have h9 : Entails.eval a c11362 := derived11362 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11365 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11365 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10363, some c10337, some c11051, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11365 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11365 : lratChecker f11365 p11365 = .success := by decide +kernel
theorem unsat11365 : Unsatisfiable (PosFin 65) f11365 := by
  apply lratCheckerSound f11365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11365
  · intro a ha; simp [p11365] at ha; subst a; trivial
  · exact checked11365
theorem derived11365 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11365 := by
  apply localUnsat_implies_entails f11365 [c10363, c10337, c11051] c11365 unsat11365 (by rfl) a
  have h0 : Entails.eval a c10363 := derived10363 a h
  have h1 : Entails.eval a c10337 := derived10337 a h
  have h2 : Entails.eval a c11051 := derived11051 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11366 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11366 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11359, some c11364, some c10771, some c10641, some c11365, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11366 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11366 : lratChecker f11366 p11366 = .success := by decide +kernel
theorem unsat11366 : Unsatisfiable (PosFin 65) f11366 := by
  apply lratCheckerSound f11366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11366
  · intro a ha; simp [p11366] at ha; subst a; trivial
  · exact checked11366
theorem derived11366 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11366 := by
  apply localUnsat_implies_entails f11366 [c11331, c11359, c11364, c10771, c10641, c11365] c11366 unsat11366 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11359 := derived11359 a h
  have h2 : Entails.eval a c11364 := derived11364 a h
  have h3 : Entails.eval a c10771 := derived10771 a h
  have h4 : Entails.eval a c10641 := derived10641 a h
  have h5 : Entails.eval a c11365 := derived11365 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11367 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11367 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11359, some c11364, some c11366, some c11361, some c10822, some c10818, some c10685, some c10383, some c10828, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11367 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11367 : lratChecker f11367 p11367 = .success := by decide +kernel
theorem unsat11367 : Unsatisfiable (PosFin 65) f11367 := by
  apply lratCheckerSound f11367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11367
  · intro a ha; simp [p11367] at ha; subst a; trivial
  · exact checked11367
theorem derived11367 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11367 := by
  apply localUnsat_implies_entails f11367 [c11331, c11359, c11364, c11366, c11361, c10822, c10818, c10685, c10383, c10828] c11367 unsat11367 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11359 := derived11359 a h
  have h2 : Entails.eval a c11364 := derived11364 a h
  have h3 : Entails.eval a c11366 := derived11366 a h
  have h4 : Entails.eval a c11361 := derived11361 a h
  have h5 : Entails.eval a c10822 := derived10822 a h
  have h6 : Entails.eval a c10818 := derived10818 a h
  have h7 : Entails.eval a c10685 := derived10685 a h
  have h8 : Entails.eval a c10383 := derived10383 a h
  have h9 : Entails.eval a c10828 := derived10828 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11368 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11368 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11359, some c11345, some c11367, some c11356, some c11360, some c11352, some c11346, some c11302, some c11350, some c4054, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11368 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11368 : lratChecker f11368 p11368 = .success := by decide +kernel
theorem unsat11368 : Unsatisfiable (PosFin 65) f11368 := by
  apply lratCheckerSound f11368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11368
  · intro a ha; simp [p11368] at ha; subst a; trivial
  · exact checked11368
theorem derived11368 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11368 := by
  apply localUnsat_implies_entails f11368 [c11170, c11359, c11345, c11367, c11356, c11360, c11352, c11346, c11302, c11350, c4054] c11368 unsat11368 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11359 := derived11359 a h
  have h2 : Entails.eval a c11345 := derived11345 a h
  have h3 : Entails.eval a c11367 := derived11367 a h
  have h4 : Entails.eval a c11356 := derived11356 a h
  have h5 : Entails.eval a c11360 := derived11360 a h
  have h6 : Entails.eval a c11352 := derived11352 a h
  have h7 : Entails.eval a c11346 := derived11346 a h
  have h8 : Entails.eval a c11302 := derived11302 a h
  have h9 : Entails.eval a c11350 := derived11350 a h
  have h10 : Entails.eval a c4054 := h 4053 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11369 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨34, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11369 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c4993, some c4991, some c4992, some c4071, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11369 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11369 : lratChecker f11369 p11369 = .success := by decide +kernel
theorem unsat11369 : Unsatisfiable (PosFin 65) f11369 := by
  apply lratCheckerSound f11369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11369
  · intro a ha; simp [p11369] at ha; subst a; trivial
  · exact checked11369
theorem derived11369 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11369 := by
  apply localUnsat_implies_entails f11369 [c11170, c11256, c4993, c4991, c4992, c4071] c11369 unsat11369 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c4993 := h 4992 (by decide)
  have h3 : Entails.eval a c4991 := h 4990 (by decide)
  have h4 : Entails.eval a c4992 := h 4991 (by decide)
  have h5 : Entails.eval a c4071 := h 4070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11370 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11370 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11345, some c11359, some c11356, some c11352, some c11302, some c11350, some c4989, some c11369, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11370 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11370 : lratChecker f11370 p11370 = .success := by decide +kernel
theorem unsat11370 : Unsatisfiable (PosFin 65) f11370 := by
  apply lratCheckerSound f11370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11370
  · intro a ha; simp [p11370] at ha; subst a; trivial
  · exact checked11370
theorem derived11370 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11370 := by
  apply localUnsat_implies_entails f11370 [c11256, c11345, c11359, c11356, c11352, c11302, c11350, c4989, c11369] c11370 unsat11370 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11345 := derived11345 a h
  have h2 : Entails.eval a c11359 := derived11359 a h
  have h3 : Entails.eval a c11356 := derived11356 a h
  have h4 : Entails.eval a c11352 := derived11352 a h
  have h5 : Entails.eval a c11302 := derived11302 a h
  have h6 : Entails.eval a c11350 := derived11350 a h
  have h7 : Entails.eval a c4989 := h 4988 (by decide)
  have h8 : Entails.eval a c11369 := derived11369 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11371 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨23, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11371 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11170, some c4057, some c4058, some c4980, some c4988, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11371 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11371 : lratChecker f11371 p11371 = .success := by decide +kernel
theorem unsat11371 : Unsatisfiable (PosFin 65) f11371 := by
  apply lratCheckerSound f11371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11371
  · intro a ha; simp [p11371] at ha; subst a; trivial
  · exact checked11371
theorem derived11371 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11371 := by
  apply localUnsat_implies_entails f11371 [c11256, c11170, c4057, c4058, c4980, c4988] c11371 unsat11371 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c4057 := h 4056 (by decide)
  have h3 : Entails.eval a c4058 := h 4057 (by decide)
  have h4 : Entails.eval a c4980 := h 4979 (by decide)
  have h5 : Entails.eval a c4988 := h 4987 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11372 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11372 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11368, some c11359, some c11345, some c11356, some c11352, some c11370, some c11346, some c11371, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11372 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11372 : lratChecker f11372 p11372 = .success := by decide +kernel
theorem unsat11372 : Unsatisfiable (PosFin 65) f11372 := by
  apply lratCheckerSound f11372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11372
  · intro a ha; simp [p11372] at ha; subst a; trivial
  · exact checked11372
theorem derived11372 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11372 := by
  apply localUnsat_implies_entails f11372 [c11368, c11359, c11345, c11356, c11352, c11370, c11346, c11371] c11372 unsat11372 (by rfl) a
  have h0 : Entails.eval a c11368 := derived11368 a h
  have h1 : Entails.eval a c11359 := derived11359 a h
  have h2 : Entails.eval a c11345 := derived11345 a h
  have h3 : Entails.eval a c11356 := derived11356 a h
  have h4 : Entails.eval a c11352 := derived11352 a h
  have h5 : Entails.eval a c11370 := derived11370 a h
  have h6 : Entails.eval a c11346 := derived11346 a h
  have h7 : Entails.eval a c11371 := derived11371 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11373 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11373 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10773, some c10511, some c10775, some c10691, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11373 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11373 : lratChecker f11373 p11373 = .success := by decide +kernel
theorem unsat11373 : Unsatisfiable (PosFin 65) f11373 := by
  apply lratCheckerSound f11373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11373
  · intro a ha; simp [p11373] at ha; subst a; trivial
  · exact checked11373
theorem derived11373 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11373 := by
  apply localUnsat_implies_entails f11373 [c10773, c10511, c10775, c10691] c11373 unsat11373 (by rfl) a
  have h0 : Entails.eval a c10773 := derived10773 a h
  have h1 : Entails.eval a c10511 := derived10511 a h
  have h2 : Entails.eval a c10775 := derived10775 a h
  have h3 : Entails.eval a c10691 := derived10691 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11374 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11374 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11372, some c11368, some c11373, some c11210, some c10694, some c10691, some c10830, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11374 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11374 : lratChecker f11374 p11374 = .success := by decide +kernel
theorem unsat11374 : Unsatisfiable (PosFin 65) f11374 := by
  apply lratCheckerSound f11374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11374
  · intro a ha; simp [p11374] at ha; subst a; trivial
  · exact checked11374
theorem derived11374 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11374 := by
  apply localUnsat_implies_entails f11374 [c11372, c11368, c11373, c11210, c10694, c10691, c10830] c11374 unsat11374 (by rfl) a
  have h0 : Entails.eval a c11372 := derived11372 a h
  have h1 : Entails.eval a c11368 := derived11368 a h
  have h2 : Entails.eval a c11373 := derived11373 a h
  have h3 : Entails.eval a c11210 := derived11210 a h
  have h4 : Entails.eval a c10694 := derived10694 a h
  have h5 : Entails.eval a c10691 := derived10691 a h
  have h6 : Entails.eval a c10830 := derived10830 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11375 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11375 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11170, some c11372, some c11368, some c11373, some c11210, some c11359, some c11345, some c11374, some c10497, some c10802, some c10822, some c10818, some c10484, some c10685, some c10830, some c10828, some c10641, some c10689, some c11365, some c10921, some c10323, some c10636, some c10652, some c10779, some c974, some c972, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11375 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked11375 : lratChecker f11375 p11375 = .success := by decide +kernel
theorem unsat11375 : Unsatisfiable (PosFin 65) f11375 := by
  apply lratCheckerSound f11375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11375
  · intro a ha; simp [p11375] at ha; subst a; trivial
  · exact checked11375
theorem derived11375 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11375 := by
  apply localUnsat_implies_entails f11375 [c11331, c11170, c11372, c11368, c11373, c11210, c11359, c11345, c11374, c10497, c10802, c10822, c10818, c10484, c10685, c10830, c10828, c10641, c10689, c11365, c10921, c10323, c10636, c10652, c10779, c974, c972] c11375 unsat11375 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11372 := derived11372 a h
  have h3 : Entails.eval a c11368 := derived11368 a h
  have h4 : Entails.eval a c11373 := derived11373 a h
  have h5 : Entails.eval a c11210 := derived11210 a h
  have h6 : Entails.eval a c11359 := derived11359 a h
  have h7 : Entails.eval a c11345 := derived11345 a h
  have h8 : Entails.eval a c11374 := derived11374 a h
  have h9 : Entails.eval a c10497 := derived10497 a h
  have h10 : Entails.eval a c10802 := derived10802 a h
  have h11 : Entails.eval a c10822 := derived10822 a h
  have h12 : Entails.eval a c10818 := derived10818 a h
  have h13 : Entails.eval a c10484 := derived10484 a h
  have h14 : Entails.eval a c10685 := derived10685 a h
  have h15 : Entails.eval a c10830 := derived10830 a h
  have h16 : Entails.eval a c10828 := derived10828 a h
  have h17 : Entails.eval a c10641 := derived10641 a h
  have h18 : Entails.eval a c10689 := derived10689 a h
  have h19 : Entails.eval a c11365 := derived11365 a h
  have h20 : Entails.eval a c10921 := derived10921 a h
  have h21 : Entails.eval a c10323 := derived10323 a h
  have h22 : Entails.eval a c10636 := derived10636 a h
  have h23 : Entails.eval a c10652 := derived10652 a h
  have h24 : Entails.eval a c10779 := derived10779 a h
  have h25 : Entails.eval a c974 := h 973 (by decide)
  have h26 : Entails.eval a c972 := h 971 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11376 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11376 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11373, some c11375, some c10504, some c10768, some c10818, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11376 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11376 : lratChecker f11376 p11376 = .success := by decide +kernel
theorem unsat11376 : Unsatisfiable (PosFin 65) f11376 := by
  apply lratCheckerSound f11376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11376
  · intro a ha; simp [p11376] at ha; subst a; trivial
  · exact checked11376
theorem derived11376 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11376 := by
  apply localUnsat_implies_entails f11376 [c11331, c11373, c11375, c10504, c10768, c10818] c11376 unsat11376 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11373 := derived11373 a h
  have h2 : Entails.eval a c11375 := derived11375 a h
  have h3 : Entails.eval a c10504 := derived10504 a h
  have h4 : Entails.eval a c10768 := derived10768 a h
  have h5 : Entails.eval a c10818 := derived10818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11377 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11377 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11368, some c11372, some c11376, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11377 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11377 : lratChecker f11377 p11377 = .success := by decide +kernel
theorem unsat11377 : Unsatisfiable (PosFin 65) f11377 := by
  apply lratCheckerSound f11377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11377
  · intro a ha; simp [p11377] at ha; subst a; trivial
  · exact checked11377
theorem derived11377 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11377 := by
  apply localUnsat_implies_entails f11377 [c11368, c11372, c11376] c11377 unsat11377 (by rfl) a
  have h0 : Entails.eval a c11368 := derived11368 a h
  have h1 : Entails.eval a c11372 := derived11372 a h
  have h2 : Entails.eval a c11376 := derived11376 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11378 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11378 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10504, some c10740, some c10818, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11378 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11378 : lratChecker f11378 p11378 = .success := by decide +kernel
theorem unsat11378 : Unsatisfiable (PosFin 65) f11378 := by
  apply lratCheckerSound f11378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11378
  · intro a ha; simp [p11378] at ha; subst a; trivial
  · exact checked11378
theorem derived11378 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11378 := by
  apply localUnsat_implies_entails f11378 [c11331, c10504, c10740, c10818] c11378 unsat11378 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10504 := derived10504 a h
  have h2 : Entails.eval a c10740 := derived10740 a h
  have h3 : Entails.eval a c10818 := derived10818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11379 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11379 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10823, some c10818, some c10685, some c10763, some c10828, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11379 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11379 : lratChecker f11379 p11379 = .success := by decide +kernel
theorem unsat11379 : Unsatisfiable (PosFin 65) f11379 := by
  apply lratCheckerSound f11379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11379
  · intro a ha; simp [p11379] at ha; subst a; trivial
  · exact checked11379
theorem derived11379 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11379 := by
  apply localUnsat_implies_entails f11379 [c11331, c10823, c10818, c10685, c10763, c10828] c11379 unsat11379 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10823 := derived10823 a h
  have h2 : Entails.eval a c10818 := derived10818 a h
  have h3 : Entails.eval a c10685 := derived10685 a h
  have h4 : Entails.eval a c10763 := derived10763 a h
  have h5 : Entails.eval a c10828 := derived10828 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11380 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨22, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11380 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11377, some c11170, some c11018, some c329, some c327, some c321, some c323, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p11380 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11380 : lratChecker f11380 p11380 = .success := by decide +kernel
theorem unsat11380 : Unsatisfiable (PosFin 65) f11380 := by
  apply lratCheckerSound f11380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11380
  · intro a ha; simp [p11380] at ha; subst a; trivial
  · exact checked11380
theorem derived11380 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11380 := by
  apply localUnsat_implies_entails f11380 [c11377, c11170, c11018, c329, c327, c321, c323] c11380 unsat11380 (by rfl) a
  have h0 : Entails.eval a c11377 := derived11377 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11018 := derived11018 a h
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c327 := h 326 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11381 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11381 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11377, some c11018, some c11331, some c11378, some c11379, some c10503, some c10766, some c10486, some c10828, some c10658, some c10739, some c10429, some c11205, some c11380, some c10769, some c10712, some c319, some c10310, some c332, some c316, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11381 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked11381 : lratChecker f11381 p11381 = .success := by decide +kernel
theorem unsat11381 : Unsatisfiable (PosFin 65) f11381 := by
  apply lratCheckerSound f11381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11381
  · intro a ha; simp [p11381] at ha; subst a; trivial
  · exact checked11381
theorem derived11381 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11381 := by
  apply localUnsat_implies_entails f11381 [c11170, c11377, c11018, c11331, c11378, c11379, c10503, c10766, c10486, c10828, c10658, c10739, c10429, c11205, c11380, c10769, c10712, c319, c10310, c332, c316] c11381 unsat11381 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11018 := derived11018 a h
  have h3 : Entails.eval a c11331 := derived11331 a h
  have h4 : Entails.eval a c11378 := derived11378 a h
  have h5 : Entails.eval a c11379 := derived11379 a h
  have h6 : Entails.eval a c10503 := derived10503 a h
  have h7 : Entails.eval a c10766 := derived10766 a h
  have h8 : Entails.eval a c10486 := derived10486 a h
  have h9 : Entails.eval a c10828 := derived10828 a h
  have h10 : Entails.eval a c10658 := derived10658 a h
  have h11 : Entails.eval a c10739 := derived10739 a h
  have h12 : Entails.eval a c10429 := derived10429 a h
  have h13 : Entails.eval a c11205 := derived11205 a h
  have h14 : Entails.eval a c11380 := derived11380 a h
  have h15 : Entails.eval a c10769 := derived10769 a h
  have h16 : Entails.eval a c10712 := derived10712 a h
  have h17 : Entails.eval a c319 := h 318 (by decide)
  have h18 : Entails.eval a c10310 := derived10310 a h
  have h19 : Entails.eval a c332 := h 331 (by decide)
  have h20 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11382 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11382 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11381, some c10774, some c10808, some c10483, some c10460, some c10421, some c11363, some c10769, some c10712, some c10641, some c10215, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11382 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11382 : lratChecker f11382 p11382 = .success := by decide +kernel
theorem unsat11382 : Unsatisfiable (PosFin 65) f11382 := by
  apply lratCheckerSound f11382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11382
  · intro a ha; simp [p11382] at ha; subst a; trivial
  · exact checked11382
theorem derived11382 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11382 := by
  apply localUnsat_implies_entails f11382 [c11331, c11381, c10774, c10808, c10483, c10460, c10421, c11363, c10769, c10712, c10641, c10215] c11382 unsat11382 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11381 := derived11381 a h
  have h2 : Entails.eval a c10774 := derived10774 a h
  have h3 : Entails.eval a c10808 := derived10808 a h
  have h4 : Entails.eval a c10483 := derived10483 a h
  have h5 : Entails.eval a c10460 := derived10460 a h
  have h6 : Entails.eval a c10421 := derived10421 a h
  have h7 : Entails.eval a c11363 := derived11363 a h
  have h8 : Entails.eval a c10769 := derived10769 a h
  have h9 : Entails.eval a c10712 := derived10712 a h
  have h10 : Entails.eval a c10641 := derived10641 a h
  have h11 : Entails.eval a c10215 := derived10215 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11383 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11383 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11381, some c10774, some c11363, some c10808, some c10215, some c10310, some c10747, some c10471, some c10210, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11383 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11383 : lratChecker f11383 p11383 = .success := by decide +kernel
theorem unsat11383 : Unsatisfiable (PosFin 65) f11383 := by
  apply lratCheckerSound f11383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11383
  · intro a ha; simp [p11383] at ha; subst a; trivial
  · exact checked11383
theorem derived11383 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11383 := by
  apply localUnsat_implies_entails f11383 [c11331, c11381, c10774, c11363, c10808, c10215, c10310, c10747, c10471, c10210] c11383 unsat11383 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11381 := derived11381 a h
  have h2 : Entails.eval a c10774 := derived10774 a h
  have h3 : Entails.eval a c11363 := derived11363 a h
  have h4 : Entails.eval a c10808 := derived10808 a h
  have h5 : Entails.eval a c10215 := derived10215 a h
  have h6 : Entails.eval a c10310 := derived10310 a h
  have h7 : Entails.eval a c10747 := derived10747 a h
  have h8 : Entails.eval a c10471 := derived10471 a h
  have h9 : Entails.eval a c10210 := derived10210 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11384 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11384 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11381, some c10774, some c10808, some c10486, some c10763, some c10483, some c10460, some c11383, some c11051, some c10713, some c10326, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11384 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11384 : lratChecker f11384 p11384 = .success := by decide +kernel
theorem unsat11384 : Unsatisfiable (PosFin 65) f11384 := by
  apply lratCheckerSound f11384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11384
  · intro a ha; simp [p11384] at ha; subst a; trivial
  · exact checked11384
theorem derived11384 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11384 := by
  apply localUnsat_implies_entails f11384 [c11331, c11381, c10774, c10808, c10486, c10763, c10483, c10460, c11383, c11051, c10713, c10326] c11384 unsat11384 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11381 := derived11381 a h
  have h2 : Entails.eval a c10774 := derived10774 a h
  have h3 : Entails.eval a c10808 := derived10808 a h
  have h4 : Entails.eval a c10486 := derived10486 a h
  have h5 : Entails.eval a c10763 := derived10763 a h
  have h6 : Entails.eval a c10483 := derived10483 a h
  have h7 : Entails.eval a c10460 := derived10460 a h
  have h8 : Entails.eval a c11383 := derived11383 a h
  have h9 : Entails.eval a c11051 := derived11051 a h
  have h10 : Entails.eval a c10713 := derived10713 a h
  have h11 : Entails.eval a c10326 := derived10326 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11385 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨51, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11385 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10778, some c10289, some c10313, some c10293, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11385 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11385 : lratChecker f11385 p11385 = .success := by decide +kernel
theorem unsat11385 : Unsatisfiable (PosFin 65) f11385 := by
  apply lratCheckerSound f11385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11385
  · intro a ha; simp [p11385] at ha; subst a; trivial
  · exact checked11385
theorem derived11385 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11385 := by
  apply localUnsat_implies_entails f11385 [c11331, c10778, c10289, c10313, c10293] c11385 unsat11385 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10778 := derived10778 a h
  have h2 : Entails.eval a c10289 := derived10289 a h
  have h3 : Entails.eval a c10313 := derived10313 a h
  have h4 : Entails.eval a c10293 := derived10293 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11386 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11386 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10774, some c10808, some c11382, some c11384, some c10473, some c11385, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11386 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11386 : lratChecker f11386 p11386 = .success := by decide +kernel
theorem unsat11386 : Unsatisfiable (PosFin 65) f11386 := by
  apply lratCheckerSound f11386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11386
  · intro a ha; simp [p11386] at ha; subst a; trivial
  · exact checked11386
theorem derived11386 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11386 := by
  apply localUnsat_implies_entails f11386 [c11331, c10774, c10808, c11382, c11384, c10473, c11385] c11386 unsat11386 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10774 := derived10774 a h
  have h2 : Entails.eval a c10808 := derived10808 a h
  have h3 : Entails.eval a c11382 := derived11382 a h
  have h4 : Entails.eval a c11384 := derived11384 a h
  have h5 : Entails.eval a c10473 := derived10473 a h
  have h6 : Entails.eval a c11385 := derived11385 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11387 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11387 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11381, some c11386, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11387 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11387 : lratChecker f11387 p11387 = .success := by decide +kernel
theorem unsat11387 : Unsatisfiable (PosFin 65) f11387 := by
  apply lratCheckerSound f11387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11387
  · intro a ha; simp [p11387] at ha; subst a; trivial
  · exact checked11387
theorem derived11387 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11387 := by
  apply localUnsat_implies_entails f11387 [c11381, c11386] c11387 unsat11387 (by rfl) a
  have h0 : Entails.eval a c11381 := derived11381 a h
  have h1 : Entails.eval a c11386 := derived11386 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11388 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11388 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11377, some c11170, some c10635, some c10756, some c10312, some c10769, some c10377, some c955, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11388 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11388 : lratChecker f11388 p11388 = .success := by decide +kernel
theorem unsat11388 : Unsatisfiable (PosFin 65) f11388 := by
  apply lratCheckerSound f11388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11388
  · intro a ha; simp [p11388] at ha; subst a; trivial
  · exact checked11388
theorem derived11388 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11388 := by
  apply localUnsat_implies_entails f11388 [c11331, c11377, c11170, c10635, c10756, c10312, c10769, c10377, c955] c11388 unsat11388 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c10635 := derived10635 a h
  have h4 : Entails.eval a c10756 := derived10756 a h
  have h5 : Entails.eval a c10312 := derived10312 a h
  have h6 : Entails.eval a c10769 := derived10769 a h
  have h7 : Entails.eval a c10377 := derived10377 a h
  have h8 : Entails.eval a c955 := h 954 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11389 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨58, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11389 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11377, some c11170, some c11385, some c11387, some c10635, some c10210, some c10779, some c11051, some c10306, some c10746, some c10323, some c11388, some c10742, some c957, some c10695, some c955, some c962, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11389 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11389 : lratChecker f11389 p11389 = .success := by decide +kernel
theorem unsat11389 : Unsatisfiable (PosFin 65) f11389 := by
  apply lratCheckerSound f11389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11389
  · intro a ha; simp [p11389] at ha; subst a; trivial
  · exact checked11389
theorem derived11389 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11389 := by
  apply localUnsat_implies_entails f11389 [c11331, c11377, c11170, c11385, c11387, c10635, c10210, c10779, c11051, c10306, c10746, c10323, c11388, c10742, c957, c10695, c955, c962] c11389 unsat11389 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11385 := derived11385 a h
  have h4 : Entails.eval a c11387 := derived11387 a h
  have h5 : Entails.eval a c10635 := derived10635 a h
  have h6 : Entails.eval a c10210 := derived10210 a h
  have h7 : Entails.eval a c10779 := derived10779 a h
  have h8 : Entails.eval a c11051 := derived11051 a h
  have h9 : Entails.eval a c10306 := derived10306 a h
  have h10 : Entails.eval a c10746 := derived10746 a h
  have h11 : Entails.eval a c10323 := derived10323 a h
  have h12 : Entails.eval a c11388 := derived11388 a h
  have h13 : Entails.eval a c10742 := derived10742 a h
  have h14 : Entails.eval a c957 := h 956 (by decide)
  have h15 : Entails.eval a c10695 := derived10695 a h
  have h16 : Entails.eval a c955 := h 954 (by decide)
  have h17 : Entails.eval a c962 := h 961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11390 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨21, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11390 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11377, some c11018, some c319, some c332, some c322, some c316, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p11390 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11390 : lratChecker f11390 p11390 = .success := by decide +kernel
theorem unsat11390 : Unsatisfiable (PosFin 65) f11390 := by
  apply lratCheckerSound f11390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11390
  · intro a ha; simp [p11390] at ha; subst a; trivial
  · exact checked11390
theorem derived11390 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11390 := by
  apply localUnsat_implies_entails f11390 [c11170, c11377, c11018, c319, c332, c322, c316] c11390 unsat11390 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11018 := derived11018 a h
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11391 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨55, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11391 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11387, some c10742, some c10695, some c10705, some c10421, some c10683, some c10664, some c10772, some c11390, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11391 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11391 : lratChecker f11391 p11391 = .success := by decide +kernel
theorem unsat11391 : Unsatisfiable (PosFin 65) f11391 := by
  apply lratCheckerSound f11391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11391
  · intro a ha; simp [p11391] at ha; subst a; trivial
  · exact checked11391
theorem derived11391 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11391 := by
  apply localUnsat_implies_entails f11391 [c11331, c11387, c10742, c10695, c10705, c10421, c10683, c10664, c10772, c11390] c11391 unsat11391 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11387 := derived11387 a h
  have h2 : Entails.eval a c10742 := derived10742 a h
  have h3 : Entails.eval a c10695 := derived10695 a h
  have h4 : Entails.eval a c10705 := derived10705 a h
  have h5 : Entails.eval a c10421 := derived10421 a h
  have h6 : Entails.eval a c10683 := derived10683 a h
  have h7 : Entails.eval a c10664 := derived10664 a h
  have h8 : Entails.eval a c10772 := derived10772 a h
  have h9 : Entails.eval a c11390 := derived11390 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11392 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11392 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10514, some c10421, some c10483, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11392 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11392 : lratChecker f11392 p11392 = .success := by decide +kernel
theorem unsat11392 : Unsatisfiable (PosFin 65) f11392 := by
  apply lratCheckerSound f11392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11392
  · intro a ha; simp [p11392] at ha; subst a; trivial
  · exact checked11392
theorem derived11392 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11392 := by
  apply localUnsat_implies_entails f11392 [c11331, c10514, c10421, c10483] c11392 unsat11392 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10514 := derived10514 a h
  have h2 : Entails.eval a c10421 := derived10421 a h
  have h3 : Entails.eval a c10483 := derived10483 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11393 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11393 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11387, some c11392, some c10695, some c10509, some c10460, some c10483, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11393 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11393 : lratChecker f11393 p11393 = .success := by decide +kernel
theorem unsat11393 : Unsatisfiable (PosFin 65) f11393 := by
  apply lratCheckerSound f11393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11393
  · intro a ha; simp [p11393] at ha; subst a; trivial
  · exact checked11393
theorem derived11393 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11393 := by
  apply localUnsat_implies_entails f11393 [c11331, c11387, c11392, c10695, c10509, c10460, c10483] c11393 unsat11393 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11387 := derived11387 a h
  have h2 : Entails.eval a c11392 := derived11392 a h
  have h3 : Entails.eval a c10695 := derived10695 a h
  have h4 : Entails.eval a c10509 := derived10509 a h
  have h5 : Entails.eval a c10460 := derived10460 a h
  have h6 : Entails.eval a c10483 := derived10483 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11394 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11394 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11387, some c11393, some c10742, some c11391, some c10695, some c10705, some c11389, some c10514, some c10499, some c10314, some c10652, some c10471, some c10316, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11394 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11394 : lratChecker f11394 p11394 = .success := by decide +kernel
theorem unsat11394 : Unsatisfiable (PosFin 65) f11394 := by
  apply lratCheckerSound f11394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11394
  · intro a ha; simp [p11394] at ha; subst a; trivial
  · exact checked11394
theorem derived11394 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11394 := by
  apply localUnsat_implies_entails f11394 [c11331, c11387, c11393, c10742, c11391, c10695, c10705, c11389, c10514, c10499, c10314, c10652, c10471, c10316] c11394 unsat11394 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11387 := derived11387 a h
  have h2 : Entails.eval a c11393 := derived11393 a h
  have h3 : Entails.eval a c10742 := derived10742 a h
  have h4 : Entails.eval a c11391 := derived11391 a h
  have h5 : Entails.eval a c10695 := derived10695 a h
  have h6 : Entails.eval a c10705 := derived10705 a h
  have h7 : Entails.eval a c11389 := derived11389 a h
  have h8 : Entails.eval a c10514 := derived10514 a h
  have h9 : Entails.eval a c10499 := derived10499 a h
  have h10 : Entails.eval a c10314 := derived10314 a h
  have h11 : Entails.eval a c10652 := derived10652 a h
  have h12 : Entails.eval a c10471 := derived10471 a h
  have h13 : Entails.eval a c10316 := derived10316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11395 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11395 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11394, some c11387, some c10695, some c10705, some c10418, some c10451, some c10818, some c10668, some c10499, some c10804, some c10483, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11395 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11395 : lratChecker f11395 p11395 = .success := by decide +kernel
theorem unsat11395 : Unsatisfiable (PosFin 65) f11395 := by
  apply lratCheckerSound f11395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11395
  · intro a ha; simp [p11395] at ha; subst a; trivial
  · exact checked11395
theorem derived11395 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11395 := by
  apply localUnsat_implies_entails f11395 [c11331, c11394, c11387, c10695, c10705, c10418, c10451, c10818, c10668, c10499, c10804, c10483] c11395 unsat11395 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11394 := derived11394 a h
  have h2 : Entails.eval a c11387 := derived11387 a h
  have h3 : Entails.eval a c10695 := derived10695 a h
  have h4 : Entails.eval a c10705 := derived10705 a h
  have h5 : Entails.eval a c10418 := derived10418 a h
  have h6 : Entails.eval a c10451 := derived10451 a h
  have h7 : Entails.eval a c10818 := derived10818 a h
  have h8 : Entails.eval a c10668 := derived10668 a h
  have h9 : Entails.eval a c10499 := derived10499 a h
  have h10 : Entails.eval a c10804 := derived10804 a h
  have h11 : Entails.eval a c10483 := derived10483 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11396 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11396 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10483, some c10486, some c10450, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11396 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11396 : lratChecker f11396 p11396 = .success := by decide +kernel
theorem unsat11396 : Unsatisfiable (PosFin 65) f11396 := by
  apply lratCheckerSound f11396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11396
  · intro a ha; simp [p11396] at ha; subst a; trivial
  · exact checked11396
theorem derived11396 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11396 := by
  apply localUnsat_implies_entails f11396 [c11331, c10483, c10486, c10450] c11396 unsat11396 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10483 := derived10483 a h
  have h2 : Entails.eval a c10486 := derived10486 a h
  have h3 : Entails.eval a c10450 := derived10450 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11397 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11397 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11395, some c11387, some c10658, some c10802, some c10665, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11397 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11397 : lratChecker f11397 p11397 = .success := by decide +kernel
theorem unsat11397 : Unsatisfiable (PosFin 65) f11397 := by
  apply lratCheckerSound f11397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11397
  · intro a ha; simp [p11397] at ha; subst a; trivial
  · exact checked11397
theorem derived11397 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11397 := by
  apply localUnsat_implies_entails f11397 [c11331, c11395, c11387, c10658, c10802, c10665] c11397 unsat11397 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11395 := derived11395 a h
  have h2 : Entails.eval a c11387 := derived11387 a h
  have h3 : Entails.eval a c10658 := derived10658 a h
  have h4 : Entails.eval a c10802 := derived10802 a h
  have h5 : Entails.eval a c10665 := derived10665 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11398 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11398 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11397, some c11395, some c10483, some c11396, some c10408, some c10770, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11398 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11398 : lratChecker f11398 p11398 = .success := by decide +kernel
theorem unsat11398 : Unsatisfiable (PosFin 65) f11398 := by
  apply lratCheckerSound f11398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11398
  · intro a ha; simp [p11398] at ha; subst a; trivial
  · exact checked11398
theorem derived11398 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11398 := by
  apply localUnsat_implies_entails f11398 [c11331, c11397, c11395, c10483, c11396, c10408, c10770] c11398 unsat11398 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11397 := derived11397 a h
  have h2 : Entails.eval a c11395 := derived11395 a h
  have h3 : Entails.eval a c10483 := derived10483 a h
  have h4 : Entails.eval a c11396 := derived11396 a h
  have h5 : Entails.eval a c10408 := derived10408 a h
  have h6 : Entails.eval a c10770 := derived10770 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11399 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨55, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11399 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11377, some c11170, some c11394, some c11395, some c11398, some c10500, some c10818, some c10823, some c10685, some c10828, some c10383, some c11397, some c11387, some c11385, some c10635, some c10689, some c10641, some c10210, some c10323, some c953, some c967, some c954, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11399 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked11399 : lratChecker f11399 p11399 = .success := by decide +kernel
theorem unsat11399 : Unsatisfiable (PosFin 65) f11399 := by
  apply lratCheckerSound f11399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11399
  · intro a ha; simp [p11399] at ha; subst a; trivial
  · exact checked11399
theorem derived11399 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11399 := by
  apply localUnsat_implies_entails f11399 [c11331, c11377, c11170, c11394, c11395, c11398, c10500, c10818, c10823, c10685, c10828, c10383, c11397, c11387, c11385, c10635, c10689, c10641, c10210, c10323, c953, c967, c954] c11399 unsat11399 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11394 := derived11394 a h
  have h4 : Entails.eval a c11395 := derived11395 a h
  have h5 : Entails.eval a c11398 := derived11398 a h
  have h6 : Entails.eval a c10500 := derived10500 a h
  have h7 : Entails.eval a c10818 := derived10818 a h
  have h8 : Entails.eval a c10823 := derived10823 a h
  have h9 : Entails.eval a c10685 := derived10685 a h
  have h10 : Entails.eval a c10828 := derived10828 a h
  have h11 : Entails.eval a c10383 := derived10383 a h
  have h12 : Entails.eval a c11397 := derived11397 a h
  have h13 : Entails.eval a c11387 := derived11387 a h
  have h14 : Entails.eval a c11385 := derived11385 a h
  have h15 : Entails.eval a c10635 := derived10635 a h
  have h16 : Entails.eval a c10689 := derived10689 a h
  have h17 : Entails.eval a c10641 := derived10641 a h
  have h18 : Entails.eval a c10210 := derived10210 a h
  have h19 : Entails.eval a c10323 := derived10323 a h
  have h20 : Entails.eval a c953 := h 952 (by decide)
  have h21 : Entails.eval a c967 := h 966 (by decide)
  have h22 : Entails.eval a c954 := h 953 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11400 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11400 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11394, some c11395, some c11398, some c10500, some c10823, some c10818, some c10685, some c11397, some c11399, some c10314, some c10471, some c10474, some c10315, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11400 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11400 : lratChecker f11400 p11400 = .success := by decide +kernel
theorem unsat11400 : Unsatisfiable (PosFin 65) f11400 := by
  apply lratCheckerSound f11400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11400
  · intro a ha; simp [p11400] at ha; subst a; trivial
  · exact checked11400
theorem derived11400 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11400 := by
  apply localUnsat_implies_entails f11400 [c11331, c11394, c11395, c11398, c10500, c10823, c10818, c10685, c11397, c11399, c10314, c10471, c10474, c10315] c11400 unsat11400 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11394 := derived11394 a h
  have h2 : Entails.eval a c11395 := derived11395 a h
  have h3 : Entails.eval a c11398 := derived11398 a h
  have h4 : Entails.eval a c10500 := derived10500 a h
  have h5 : Entails.eval a c10823 := derived10823 a h
  have h6 : Entails.eval a c10818 := derived10818 a h
  have h7 : Entails.eval a c10685 := derived10685 a h
  have h8 : Entails.eval a c11397 := derived11397 a h
  have h9 : Entails.eval a c11399 := derived11399 a h
  have h10 : Entails.eval a c10314 := derived10314 a h
  have h11 : Entails.eval a c10471 := derived10471 a h
  have h12 : Entails.eval a c10474 := derived10474 a h
  have h13 : Entails.eval a c10315 := derived10315 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11401 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11401 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11400, some c11394, some c11395, some c11398, some c10500, some c10823, some c10818, some c10685, some c11397, some c10471, some c10474, some c10524, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11401 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11401 : lratChecker f11401 p11401 = .success := by decide +kernel
theorem unsat11401 : Unsatisfiable (PosFin 65) f11401 := by
  apply lratCheckerSound f11401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11401
  · intro a ha; simp [p11401] at ha; subst a; trivial
  · exact checked11401
theorem derived11401 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11401 := by
  apply localUnsat_implies_entails f11401 [c11331, c11400, c11394, c11395, c11398, c10500, c10823, c10818, c10685, c11397, c10471, c10474, c10524] c11401 unsat11401 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11400 := derived11400 a h
  have h2 : Entails.eval a c11394 := derived11394 a h
  have h3 : Entails.eval a c11395 := derived11395 a h
  have h4 : Entails.eval a c11398 := derived11398 a h
  have h5 : Entails.eval a c10500 := derived10500 a h
  have h6 : Entails.eval a c10823 := derived10823 a h
  have h7 : Entails.eval a c10818 := derived10818 a h
  have h8 : Entails.eval a c10685 := derived10685 a h
  have h9 : Entails.eval a c11397 := derived11397 a h
  have h10 : Entails.eval a c10471 := derived10471 a h
  have h11 : Entails.eval a c10474 := derived10474 a h
  have h12 : Entails.eval a c10524 := derived10524 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11402 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11402 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11387, some c11394, some c11395, some c11398, some c10500, some c10823, some c10818, some c10685, some c10828, some c10383, some c11400, some c11401, some c11385, some c10689, some c10641, some c10324, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11402 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11402 : lratChecker f11402 p11402 = .success := by decide +kernel
theorem unsat11402 : Unsatisfiable (PosFin 65) f11402 := by
  apply lratCheckerSound f11402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11402
  · intro a ha; simp [p11402] at ha; subst a; trivial
  · exact checked11402
theorem derived11402 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11402 := by
  apply localUnsat_implies_entails f11402 [c11331, c11387, c11394, c11395, c11398, c10500, c10823, c10818, c10685, c10828, c10383, c11400, c11401, c11385, c10689, c10641, c10324] c11402 unsat11402 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11387 := derived11387 a h
  have h2 : Entails.eval a c11394 := derived11394 a h
  have h3 : Entails.eval a c11395 := derived11395 a h
  have h4 : Entails.eval a c11398 := derived11398 a h
  have h5 : Entails.eval a c10500 := derived10500 a h
  have h6 : Entails.eval a c10823 := derived10823 a h
  have h7 : Entails.eval a c10818 := derived10818 a h
  have h8 : Entails.eval a c10685 := derived10685 a h
  have h9 : Entails.eval a c10828 := derived10828 a h
  have h10 : Entails.eval a c10383 := derived10383 a h
  have h11 : Entails.eval a c11400 := derived11400 a h
  have h12 : Entails.eval a c11401 := derived11401 a h
  have h13 : Entails.eval a c11385 := derived11385 a h
  have h14 : Entails.eval a c10689 := derived10689 a h
  have h15 : Entails.eval a c10641 := derived10641 a h
  have h16 : Entails.eval a c10324 := derived10324 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11403 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨8, by decide⟩, true), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11403 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11402, some c11170, some c11256, some c11018, some c10522, some c2928, some c3093, some c2520, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p11403 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11403 : lratChecker f11403 p11403 = .success := by decide +kernel
theorem unsat11403 : Unsatisfiable (PosFin 65) f11403 := by
  apply lratCheckerSound f11403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11403
  · intro a ha; simp [p11403] at ha; subst a; trivial
  · exact checked11403
theorem derived11403 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11403 := by
  apply localUnsat_implies_entails f11403 [c11331, c11402, c11170, c11256, c11018, c10522, c2928, c3093, c2520] c11403 unsat11403 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11256 := derived11256 a h
  have h4 : Entails.eval a c11018 := derived11018 a h
  have h5 : Entails.eval a c10522 := derived10522 a h
  have h6 : Entails.eval a c2928 := h 2927 (by decide)
  have h7 : Entails.eval a c3093 := h 3092 (by decide)
  have h8 : Entails.eval a c2520 := h 2519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11404 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11404 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11402, some c11018, some c5016, some c11403, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p11404 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11404 : lratChecker f11404 p11404 = .success := by decide +kernel
theorem unsat11404 : Unsatisfiable (PosFin 65) f11404 := by
  apply lratCheckerSound f11404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11404
  · intro a ha; simp [p11404] at ha; subst a; trivial
  · exact checked11404
theorem derived11404 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11404 := by
  apply localUnsat_implies_entails f11404 [c11256, c11402, c11018, c5016, c11403] c11404 unsat11404 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11018 := derived11018 a h
  have h3 : Entails.eval a c5016 := h 5015 (by decide)
  have h4 : Entails.eval a c11403 := derived11403 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11405 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11405 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11402, some c11170, some c11404, some c3084, some c3095, some c3085, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p11405 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11405 : lratChecker f11405 p11405 = .success := by decide +kernel
theorem unsat11405 : Unsatisfiable (PosFin 65) f11405 := by
  apply lratCheckerSound f11405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11405
  · intro a ha; simp [p11405] at ha; subst a; trivial
  · exact checked11405
theorem derived11405 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11405 := by
  apply localUnsat_implies_entails f11405 [c11018, c11402, c11170, c11404, c3084, c3095, c3085] c11405 unsat11405 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11404 := derived11404 a h
  have h4 : Entails.eval a c3084 := h 3083 (by decide)
  have h5 : Entails.eval a c3095 := h 3094 (by decide)
  have h6 : Entails.eval a c3085 := h 3084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11406 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11406 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11402, some c11331, some c11405, some c4161, some c3354, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p11406 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11406 : lratChecker f11406 p11406 = .success := by decide +kernel
theorem unsat11406 : Unsatisfiable (PosFin 65) f11406 := by
  apply lratCheckerSound f11406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11406
  · intro a ha; simp [p11406] at ha; subst a; trivial
  · exact checked11406
theorem derived11406 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11406 := by
  apply localUnsat_implies_entails f11406 [c11170, c11402, c11331, c11405, c4161, c3354] c11406 unsat11406 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c11405 := derived11405 a h
  have h4 : Entails.eval a c4161 := h 4160 (by decide)
  have h5 : Entails.eval a c3354 := h 3353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11407 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11407 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c11405, some c11406, some c11051, some c5011, some c5072, some c3256, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p11407 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11407 : lratChecker f11407 p11407 = .success := by decide +kernel
theorem unsat11407 : Unsatisfiable (PosFin 65) f11407 := by
  apply lratCheckerSound f11407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11407
  · intro a ha; simp [p11407] at ha; subst a; trivial
  · exact checked11407
theorem derived11407 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11407 := by
  apply localUnsat_implies_entails f11407 [c11402, c11256, c11405, c11406, c11051, c5011, c5072, c3256] c11407 unsat11407 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11405 := derived11405 a h
  have h3 : Entails.eval a c11406 := derived11406 a h
  have h4 : Entails.eval a c11051 := derived11051 a h
  have h5 : Entails.eval a c5011 := h 5010 (by decide)
  have h6 : Entails.eval a c5072 := h 5071 (by decide)
  have h7 : Entails.eval a c3256 := h 3255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11408 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11408 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11256, some c11402, some c4769, some c10491, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11408 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11408 : lratChecker f11408 p11408 = .success := by decide +kernel
theorem unsat11408 : Unsatisfiable (PosFin 65) f11408 := by
  apply lratCheckerSound f11408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11408
  · intro a ha; simp [p11408] at ha; subst a; trivial
  · exact checked11408
theorem derived11408 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11408 := by
  apply localUnsat_implies_entails f11408 [c11331, c11256, c11402, c4769, c10491] c11408 unsat11408 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c4769 := h 4768 (by decide)
  have h4 : Entails.eval a c10491 := derived10491 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11409 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨58, by decide⟩, true), (⟨60, by decide⟩, false), (⟨28, by decide⟩, false), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11409 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11377, some c11331, some c11408, some c10489, some c10386, some c10670, some c10424, some c10793, some c11047, some c10296, some c10285, some c10318, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11409 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11409 : lratChecker f11409 p11409 = .success := by decide +kernel
theorem unsat11409 : Unsatisfiable (PosFin 65) f11409 := by
  apply lratCheckerSound f11409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11409
  · intro a ha; simp [p11409] at ha; subst a; trivial
  · exact checked11409
theorem derived11409 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11409 := by
  apply localUnsat_implies_entails f11409 [c11402, c11377, c11331, c11408, c10489, c10386, c10670, c10424, c10793, c11047, c10296, c10285, c10318] c11409 unsat11409 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c11408 := derived11408 a h
  have h4 : Entails.eval a c10489 := derived10489 a h
  have h5 : Entails.eval a c10386 := derived10386 a h
  have h6 : Entails.eval a c10670 := derived10670 a h
  have h7 : Entails.eval a c10424 := derived10424 a h
  have h8 : Entails.eval a c10793 := derived10793 a h
  have h9 : Entails.eval a c11047 := derived11047 a h
  have h10 : Entails.eval a c10296 := derived10296 a h
  have h11 : Entails.eval a c10285 := derived10285 a h
  have h12 : Entails.eval a c10318 := derived10318 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11410 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨60, by decide⟩, false), (⟨28, by decide⟩, false), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11410 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11402, some c11408, some c11409, some c4753, some c4751, some c4773, some c4746, some c4758, some c4755, some c4776, some c4745, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11410 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11410 : lratChecker f11410 p11410 = .success := by decide +kernel
theorem unsat11410 : Unsatisfiable (PosFin 65) f11410 := by
  apply lratCheckerSound f11410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11410
  · intro a ha; simp [p11410] at ha; subst a; trivial
  · exact checked11410
theorem derived11410 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11410 := by
  apply localUnsat_implies_entails f11410 [c11256, c11402, c11408, c11409, c4753, c4751, c4773, c4746, c4758, c4755, c4776, c4745] c11410 unsat11410 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11408 := derived11408 a h
  have h3 : Entails.eval a c11409 := derived11409 a h
  have h4 : Entails.eval a c4753 := h 4752 (by decide)
  have h5 : Entails.eval a c4751 := h 4750 (by decide)
  have h6 : Entails.eval a c4773 := h 4772 (by decide)
  have h7 : Entails.eval a c4746 := h 4745 (by decide)
  have h8 : Entails.eval a c4758 := h 4757 (by decide)
  have h9 : Entails.eval a c4755 := h 4754 (by decide)
  have h10 : Entails.eval a c4776 := h 4775 (by decide)
  have h11 : Entails.eval a c4745 := h 4744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11411 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨58, by decide⟩, false), (⟨28, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11411 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c11331, some c10488, some c4747, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11411 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11411 : lratChecker f11411 p11411 = .success := by decide +kernel
theorem unsat11411 : Unsatisfiable (PosFin 65) f11411 := by
  apply lratCheckerSound f11411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11411
  · intro a ha; simp [p11411] at ha; subst a; trivial
  · exact checked11411
theorem derived11411 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11411 := by
  apply localUnsat_implies_entails f11411 [c11402, c11256, c11331, c10488, c4747] c11411 unsat11411 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c10488 := derived10488 a h
  have h4 : Entails.eval a c4747 := h 4746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11412 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11412 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11410, some c11411, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p11412 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11412 : lratChecker f11412 p11412 = .success := by decide +kernel
theorem unsat11412 : Unsatisfiable (PosFin 65) f11412 := by
  apply lratCheckerSound f11412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11412
  · intro a ha; simp [p11412] at ha; subst a; trivial
  · exact checked11412
theorem derived11412 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11412 := by
  apply localUnsat_implies_entails f11412 [c11410, c11411] c11412 unsat11412 (by rfl) a
  have h0 : Entails.eval a c11410 := derived11410 a h
  have h1 : Entails.eval a c11411 := derived11411 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11413 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11413 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11377, some c11170, some c10284, some c10298, some c951, some c954, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p11413 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11413 : lratChecker f11413 p11413 = .success := by decide +kernel
theorem unsat11413 : Unsatisfiable (PosFin 65) f11413 := by
  apply lratCheckerSound f11413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11413
  · intro a ha; simp [p11413] at ha; subst a; trivial
  · exact checked11413
theorem derived11413 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11413 := by
  apply localUnsat_implies_entails f11413 [c11331, c11377, c11170, c10284, c10298, c951, c954] c11413 unsat11413 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c10284 := derived10284 a h
  have h4 : Entails.eval a c10298 := derived10298 a h
  have h5 : Entails.eval a c951 := h 950 (by decide)
  have h6 : Entails.eval a c954 := h 953 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11414 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨60, by decide⟩, true), (⟨27, by decide⟩, false), (⟨30, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11414 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11413, some c8269, some c10165, some c10318, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p11414 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11414 : lratChecker f11414 p11414 = .success := by decide +kernel
theorem unsat11414 : Unsatisfiable (PosFin 65) f11414 := by
  apply lratCheckerSound f11414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11414
  · intro a ha; simp [p11414] at ha; subst a; trivial
  · exact checked11414
theorem derived11414 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11414 := by
  apply localUnsat_implies_entails f11414 [c11331, c11413, c8269, c10165, c10318] c11414 unsat11414 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11413 := derived11413 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c10165 := derived10165 a h
  have h4 : Entails.eval a c10318 := derived10318 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11415 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11415 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11412, some c11408, some c10489, some c10386, some c10449, some c10670, some c10424, some c10794, some c11414, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11415 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11415 : lratChecker f11415 p11415 = .success := by decide +kernel
theorem unsat11415 : Unsatisfiable (PosFin 65) f11415 := by
  apply lratCheckerSound f11415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11415
  · intro a ha; simp [p11415] at ha; subst a; trivial
  · exact checked11415
theorem derived11415 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11415 := by
  apply localUnsat_implies_entails f11415 [c11331, c11412, c11408, c10489, c10386, c10449, c10670, c10424, c10794, c11414] c11415 unsat11415 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11412 := derived11412 a h
  have h2 : Entails.eval a c11408 := derived11408 a h
  have h3 : Entails.eval a c10489 := derived10489 a h
  have h4 : Entails.eval a c10386 := derived10386 a h
  have h5 : Entails.eval a c10449 := derived10449 a h
  have h6 : Entails.eval a c10670 := derived10670 a h
  have h7 : Entails.eval a c10424 := derived10424 a h
  have h8 : Entails.eval a c10794 := derived10794 a h
  have h9 : Entails.eval a c11414 := derived11414 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11416 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨31, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨17, by decide⟩, true), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11416 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11170, some c11377, some c4811, some c3604, some c3850, some c3756, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p11416 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11416 : lratChecker f11416 p11416 = .success := by decide +kernel
theorem unsat11416 : Unsatisfiable (PosFin 65) f11416 := by
  apply lratCheckerSound f11416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11416
  · intro a ha; simp [p11416] at ha; subst a; trivial
  · exact checked11416
theorem derived11416 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11416 := by
  apply localUnsat_implies_entails f11416 [c11256, c11170, c11377, c4811, c3604, c3850, c3756] c11416 unsat11416 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11377 := derived11377 a h
  have h3 : Entails.eval a c4811 := h 4810 (by decide)
  have h4 : Entails.eval a c3604 := h 3603 (by decide)
  have h5 : Entails.eval a c3850 := h 3849 (by decide)
  have h6 : Entails.eval a c3756 := h 3755 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11417 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11417 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11377, some c11256, some c11408, some c11412, some c11407, some c11415, some c4753, some c4751, some c4773, some c4758, some c4755, some c4761, some c4750, some c4767, some c11416, some c1014, some c1025, some c6055, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11417 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked11417 : lratChecker f11417 p11417 = .success := by decide +kernel
theorem unsat11417 : Unsatisfiable (PosFin 65) f11417 := by
  apply lratCheckerSound f11417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11417
  · intro a ha; simp [p11417] at ha; subst a; trivial
  · exact checked11417
theorem derived11417 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11417 := by
  apply localUnsat_implies_entails f11417 [c11402, c11377, c11256, c11408, c11412, c11407, c11415, c4753, c4751, c4773, c4758, c4755, c4761, c4750, c4767, c11416, c1014, c1025, c6055] c11417 unsat11417 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11256 := derived11256 a h
  have h3 : Entails.eval a c11408 := derived11408 a h
  have h4 : Entails.eval a c11412 := derived11412 a h
  have h5 : Entails.eval a c11407 := derived11407 a h
  have h6 : Entails.eval a c11415 := derived11415 a h
  have h7 : Entails.eval a c4753 := h 4752 (by decide)
  have h8 : Entails.eval a c4751 := h 4750 (by decide)
  have h9 : Entails.eval a c4773 := h 4772 (by decide)
  have h10 : Entails.eval a c4758 := h 4757 (by decide)
  have h11 : Entails.eval a c4755 := h 4754 (by decide)
  have h12 : Entails.eval a c4761 := h 4760 (by decide)
  have h13 : Entails.eval a c4750 := h 4749 (by decide)
  have h14 : Entails.eval a c4767 := h 4766 (by decide)
  have h15 : Entails.eval a c11416 := derived11416 a h
  have h16 : Entails.eval a c1014 := h 1013 (by decide)
  have h17 : Entails.eval a c1025 := h 1024 (by decide)
  have h18 : Entails.eval a c6055 := h 6054 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11418 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11418 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11402, some c4062, some c4977, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11418 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11418 : lratChecker f11418 p11418 = .success := by decide +kernel
theorem unsat11418 : Unsatisfiable (PosFin 65) f11418 := by
  apply lratCheckerSound f11418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11418
  · intro a ha; simp [p11418] at ha; subst a; trivial
  · exact checked11418
theorem derived11418 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11418 := by
  apply localUnsat_implies_entails f11418 [c11170, c11256, c11402, c4062, c4977] c11418 unsat11418 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c4062 := h 4061 (by decide)
  have h4 : Entails.eval a c4977 := h 4976 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11419 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11419 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c11417, some c11408, some c4762, some c4749, some c4770, some c4767, some c11418, some c4812, some c10476, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11419 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11419 : lratChecker f11419 p11419 = .success := by decide +kernel
theorem unsat11419 : Unsatisfiable (PosFin 65) f11419 := by
  apply lratCheckerSound f11419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11419
  · intro a ha; simp [p11419] at ha; subst a; trivial
  · exact checked11419
theorem derived11419 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11419 := by
  apply localUnsat_implies_entails f11419 [c11402, c11256, c11417, c11408, c4762, c4749, c4770, c4767, c11418, c4812, c10476] c11419 unsat11419 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11417 := derived11417 a h
  have h3 : Entails.eval a c11408 := derived11408 a h
  have h4 : Entails.eval a c4762 := h 4761 (by decide)
  have h5 : Entails.eval a c4749 := h 4748 (by decide)
  have h6 : Entails.eval a c4770 := h 4769 (by decide)
  have h7 : Entails.eval a c4767 := h 4766 (by decide)
  have h8 : Entails.eval a c11418 := derived11418 a h
  have h9 : Entails.eval a c4812 := h 4811 (by decide)
  have h10 : Entails.eval a c10476 := derived10476 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11420 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11420 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c11377, some c11417, some c11408, some c4762, some c4770, some c4765, some c4749, some c4767, some c11418, some c11419, some c4800, some c4273, some c4926, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11420 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11420 : lratChecker f11420 p11420 = .success := by decide +kernel
theorem unsat11420 : Unsatisfiable (PosFin 65) f11420 := by
  apply lratCheckerSound f11420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11420
  · intro a ha; simp [p11420] at ha; subst a; trivial
  · exact checked11420
theorem derived11420 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11420 := by
  apply localUnsat_implies_entails f11420 [c11402, c11256, c11377, c11417, c11408, c4762, c4770, c4765, c4749, c4767, c11418, c11419, c4800, c4273, c4926] c11420 unsat11420 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11377 := derived11377 a h
  have h3 : Entails.eval a c11417 := derived11417 a h
  have h4 : Entails.eval a c11408 := derived11408 a h
  have h5 : Entails.eval a c4762 := h 4761 (by decide)
  have h6 : Entails.eval a c4770 := h 4769 (by decide)
  have h7 : Entails.eval a c4765 := h 4764 (by decide)
  have h8 : Entails.eval a c4749 := h 4748 (by decide)
  have h9 : Entails.eval a c4767 := h 4766 (by decide)
  have h10 : Entails.eval a c11418 := derived11418 a h
  have h11 : Entails.eval a c11419 := derived11419 a h
  have h12 : Entails.eval a c4800 := h 4799 (by decide)
  have h13 : Entails.eval a c4273 := h 4272 (by decide)
  have h14 : Entails.eval a c4926 := h 4925 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11421 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11421 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10506, some c10496, some c10444, some c10663, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p11421 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11421 : lratChecker f11421 p11421 = .success := by decide +kernel
theorem unsat11421 : Unsatisfiable (PosFin 65) f11421 := by
  apply lratCheckerSound f11421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11421
  · intro a ha; simp [p11421] at ha; subst a; trivial
  · exact checked11421
theorem derived11421 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11421 := by
  apply localUnsat_implies_entails f11421 [c11331, c10506, c10496, c10444, c10663] c11421 unsat11421 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10506 := derived10506 a h
  have h2 : Entails.eval a c10496 := derived10496 a h
  have h3 : Entails.eval a c10444 := derived10444 a h
  have h4 : Entails.eval a c10663 := derived10663 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11422 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11422 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11408, some c11417, some c11420, some c11421, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11422 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11422 : lratChecker f11422 p11422 = .success := by decide +kernel
theorem unsat11422 : Unsatisfiable (PosFin 65) f11422 := by
  apply lratCheckerSound f11422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11422
  · intro a ha; simp [p11422] at ha; subst a; trivial
  · exact checked11422
theorem derived11422 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11422 := by
  apply localUnsat_implies_entails f11422 [c11408, c11417, c11420, c11421] c11422 unsat11422 (by rfl) a
  have h0 : Entails.eval a c11408 := derived11408 a h
  have h1 : Entails.eval a c11417 := derived11417 a h
  have h2 : Entails.eval a c11420 := derived11420 a h
  have h3 : Entails.eval a c11421 := derived11421 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11423 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, true), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11423 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11377, some c11170, some c11331, some c10434, some c11421, some c10663, some c10409, some c11390, some c11380, some c10693, some c325, some c326, some c10414, some c320, some c330, some c317, some c318, some c10374, some c10716, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p11423 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked11423 : lratChecker f11423 p11423 = .success := by decide +kernel
theorem unsat11423 : Unsatisfiable (PosFin 65) f11423 := by
  apply lratCheckerSound f11423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11423
  · intro a ha; simp [p11423] at ha; subst a; trivial
  · exact checked11423
theorem derived11423 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11423 := by
  apply localUnsat_implies_entails f11423 [c11018, c11377, c11170, c11331, c10434, c11421, c10663, c10409, c11390, c11380, c10693, c325, c326, c10414, c320, c330, c317, c318, c10374, c10716] c11423 unsat11423 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11331 := derived11331 a h
  have h4 : Entails.eval a c10434 := derived10434 a h
  have h5 : Entails.eval a c11421 := derived11421 a h
  have h6 : Entails.eval a c10663 := derived10663 a h
  have h7 : Entails.eval a c10409 := derived10409 a h
  have h8 : Entails.eval a c11390 := derived11390 a h
  have h9 : Entails.eval a c11380 := derived11380 a h
  have h10 : Entails.eval a c10693 := derived10693 a h
  have h11 : Entails.eval a c325 := h 324 (by decide)
  have h12 : Entails.eval a c326 := h 325 (by decide)
  have h13 : Entails.eval a c10414 := derived10414 a h
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c330 := h 329 (by decide)
  have h16 : Entails.eval a c317 := h 316 (by decide)
  have h17 : Entails.eval a c318 := h 317 (by decide)
  have h18 : Entails.eval a c10374 := derived10374 a h
  have h19 : Entails.eval a c10716 := derived10716 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11424 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨9, by decide⟩, true), (⟨55, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11424 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11170, some c11331, some c3298, some c3055, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p11424 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11424 : lratChecker f11424 p11424 = .success := by decide +kernel
theorem unsat11424 : Unsatisfiable (PosFin 65) f11424 := by
  apply lratCheckerSound f11424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11424
  · intro a ha; simp [p11424] at ha; subst a; trivial
  · exact checked11424
theorem derived11424 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11424 := by
  apply localUnsat_implies_entails f11424 [c11402, c11170, c11331, c3298, c3055] c11424 unsat11424 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c3298 := h 3297 (by decide)
  have h4 : Entails.eval a c3055 := h 3054 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11425 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11425 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11331, some c11170, some c11377, some c11402, some c11256, some c11421, some c11390, some c11380, some c325, some c326, some c320, some c330, some c317, some c318, some c10300, some c10294, some c963, some c5050, some c11424, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p11425 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked11425 : lratChecker f11425 p11425 = .success := by decide +kernel
theorem unsat11425 : Unsatisfiable (PosFin 65) f11425 := by
  apply lratCheckerSound f11425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11425
  · intro a ha; simp [p11425] at ha; subst a; trivial
  · exact checked11425
theorem derived11425 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11425 := by
  apply localUnsat_implies_entails f11425 [c11018, c11331, c11170, c11377, c11402, c11256, c11421, c11390, c11380, c325, c326, c320, c330, c317, c318, c10300, c10294, c963, c5050, c11424] c11425 unsat11425 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11331 := derived11331 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11377 := derived11377 a h
  have h4 : Entails.eval a c11402 := derived11402 a h
  have h5 : Entails.eval a c11256 := derived11256 a h
  have h6 : Entails.eval a c11421 := derived11421 a h
  have h7 : Entails.eval a c11390 := derived11390 a h
  have h8 : Entails.eval a c11380 := derived11380 a h
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c330 := h 329 (by decide)
  have h13 : Entails.eval a c317 := h 316 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c10300 := derived10300 a h
  have h16 : Entails.eval a c10294 := derived10294 a h
  have h17 : Entails.eval a c963 := h 962 (by decide)
  have h18 : Entails.eval a c5050 := h 5049 (by decide)
  have h19 : Entails.eval a c11424 := derived11424 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11426 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11426 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11331, some c11256, some c11402, some c3069, some c3312, some c5064, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11426 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11426 : lratChecker f11426 p11426 = .success := by decide +kernel
theorem unsat11426 : Unsatisfiable (PosFin 65) f11426 := by
  apply lratCheckerSound f11426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11426
  · intro a ha; simp [p11426] at ha; subst a; trivial
  · exact checked11426
theorem derived11426 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11426 := by
  apply localUnsat_implies_entails f11426 [c11170, c11331, c11256, c11402, c3069, c3312, c5064] c11426 unsat11426 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11331 := derived11331 a h
  have h2 : Entails.eval a c11256 := derived11256 a h
  have h3 : Entails.eval a c11402 := derived11402 a h
  have h4 : Entails.eval a c3069 := h 3068 (by decide)
  have h5 : Entails.eval a c3312 := h 3311 (by decide)
  have h6 : Entails.eval a c5064 := h 5063 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11427 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨7, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11427 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11377, some c11170, some c11402, some c11331, some c11422, some c11421, some c10434, some c11423, some c11425, some c10409, some c10662, some c10680, some c10788, some c11426, some c3851, some c3075, some c3305, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11427 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11427 : lratChecker f11427 p11427 = .success := by decide +kernel
theorem unsat11427 : Unsatisfiable (PosFin 65) f11427 := by
  apply lratCheckerSound f11427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11427
  · intro a ha; simp [p11427] at ha; subst a; trivial
  · exact checked11427
theorem derived11427 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11427 := by
  apply localUnsat_implies_entails f11427 [c11377, c11170, c11402, c11331, c11422, c11421, c10434, c11423, c11425, c10409, c10662, c10680, c10788, c11426, c3851, c3075, c3305] c11427 unsat11427 (by rfl) a
  have h0 : Entails.eval a c11377 := derived11377 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c11331 := derived11331 a h
  have h4 : Entails.eval a c11422 := derived11422 a h
  have h5 : Entails.eval a c11421 := derived11421 a h
  have h6 : Entails.eval a c10434 := derived10434 a h
  have h7 : Entails.eval a c11423 := derived11423 a h
  have h8 : Entails.eval a c11425 := derived11425 a h
  have h9 : Entails.eval a c10409 := derived10409 a h
  have h10 : Entails.eval a c10662 := derived10662 a h
  have h11 : Entails.eval a c10680 := derived10680 a h
  have h12 : Entails.eval a c10788 := derived10788 a h
  have h13 : Entails.eval a c11426 := derived11426 a h
  have h14 : Entails.eval a c3851 := h 3850 (by decide)
  have h15 : Entails.eval a c3075 := h 3074 (by decide)
  have h16 : Entails.eval a c3305 := h 3304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11428 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11428 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11402, some c11427, some c10489, some c4651, some c4652, some c10788, some c10518, some c11371, some c4538, some c4544, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11428 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11428 : lratChecker f11428 p11428 = .success := by decide +kernel
theorem unsat11428 : Unsatisfiable (PosFin 65) f11428 := by
  apply lratCheckerSound f11428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11428
  · intro a ha; simp [p11428] at ha; subst a; trivial
  · exact checked11428
theorem derived11428 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11428 := by
  apply localUnsat_implies_entails f11428 [c11331, c11402, c11427, c10489, c4651, c4652, c10788, c10518, c11371, c4538, c4544] c11428 unsat11428 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11427 := derived11427 a h
  have h3 : Entails.eval a c10489 := derived10489 a h
  have h4 : Entails.eval a c4651 := h 4650 (by decide)
  have h5 : Entails.eval a c4652 := h 4651 (by decide)
  have h6 : Entails.eval a c10788 := derived10788 a h
  have h7 : Entails.eval a c10518 := derived10518 a h
  have h8 : Entails.eval a c11371 := derived11371 a h
  have h9 : Entails.eval a c4538 := h 4537 (by decide)
  have h10 : Entails.eval a c4544 := h 4543 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11429 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11429 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11170, some c11377, some c11427, some c10489, some c3860, some c3849, some c3850, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11429 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11429 : lratChecker f11429 p11429 = .success := by decide +kernel
theorem unsat11429 : Unsatisfiable (PosFin 65) f11429 := by
  apply lratCheckerSound f11429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11429
  · intro a ha; simp [p11429] at ha; subst a; trivial
  · exact checked11429
theorem derived11429 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11429 := by
  apply localUnsat_implies_entails f11429 [c11331, c11170, c11377, c11427, c10489, c3860, c3849, c3850] c11429 unsat11429 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11377 := derived11377 a h
  have h3 : Entails.eval a c11427 := derived11427 a h
  have h4 : Entails.eval a c10489 := derived10489 a h
  have h5 : Entails.eval a c3860 := h 3859 (by decide)
  have h6 : Entails.eval a c3849 := h 3848 (by decide)
  have h7 : Entails.eval a c3850 := h 3849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11430 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11430 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11170, some c11331, some c3319, some c3072, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11430 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11430 : lratChecker f11430 p11430 = .success := by decide +kernel
theorem unsat11430 : Unsatisfiable (PosFin 65) f11430 := by
  apply lratCheckerSound f11430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11430
  · intro a ha; simp [p11430] at ha; subst a; trivial
  · exact checked11430
theorem derived11430 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11430 := by
  apply localUnsat_implies_entails f11430 [c11402, c11170, c11331, c3319, c3072] c11430 unsat11430 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c3319 := h 3318 (by decide)
  have h4 : Entails.eval a c3072 := h 3071 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11431 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11431 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11428, some c11430, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p11431 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11431 : lratChecker f11431 p11431 = .success := by decide +kernel
theorem unsat11431 : Unsatisfiable (PosFin 65) f11431 := by
  apply lratCheckerSound f11431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11431
  · intro a ha; simp [p11431] at ha; subst a; trivial
  · exact checked11431
theorem derived11431 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11431 := by
  apply localUnsat_implies_entails f11431 [c11428, c11430] c11431 unsat11431 (by rfl) a
  have h0 : Entails.eval a c11428 := derived11428 a h
  have h1 : Entails.eval a c11430 := derived11430 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11432 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨7, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11432 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10489, some c11429, some c4651, some c11431, some c4650, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11432 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11432 : lratChecker f11432 p11432 = .success := by decide +kernel
theorem unsat11432 : Unsatisfiable (PosFin 65) f11432 := by
  apply lratCheckerSound f11432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11432
  · intro a ha; simp [p11432] at ha; subst a; trivial
  · exact checked11432
theorem derived11432 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11432 := by
  apply localUnsat_implies_entails f11432 [c11331, c10489, c11429, c4651, c11431, c4650] c11432 unsat11432 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10489 := derived10489 a h
  have h2 : Entails.eval a c11429 := derived11429 a h
  have h3 : Entails.eval a c4651 := h 4650 (by decide)
  have h4 : Entails.eval a c11431 := derived11431 a h
  have h5 : Entails.eval a c4650 := h 4649 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11433 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11433 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11427, some c11432, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11433 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11433 : lratChecker f11433 p11433 = .success := by decide +kernel
theorem unsat11433 : Unsatisfiable (PosFin 65) f11433 := by
  apply lratCheckerSound f11433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11433
  · intro a ha; simp [p11433] at ha; subst a; trivial
  · exact checked11433
theorem derived11433 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11433 := by
  apply localUnsat_implies_entails f11433 [c11427, c11432] c11433 unsat11433 (by rfl) a
  have h0 : Entails.eval a c11427 := derived11427 a h
  have h1 : Entails.eval a c11432 := derived11432 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11434 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false), (⟨28, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11434 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11377, some c11256, some c4806, some c3854, some c3607, some c3759, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p11434 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11434 : lratChecker f11434 p11434 = .success := by decide +kernel
theorem unsat11434 : Unsatisfiable (PosFin 65) f11434 := by
  apply lratCheckerSound f11434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11434
  · intro a ha; simp [p11434] at ha; subst a; trivial
  · exact checked11434
theorem derived11434 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11434 := by
  apply localUnsat_implies_entails f11434 [c11170, c11377, c11256, c4806, c3854, c3607, c3759] c11434 unsat11434 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11256 := derived11256 a h
  have h3 : Entails.eval a c4806 := h 4805 (by decide)
  have h4 : Entails.eval a c3854 := h 3853 (by decide)
  have h5 : Entails.eval a c3607 := h 3606 (by decide)
  have h6 : Entails.eval a c3759 := h 3758 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11435 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11435 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11170, some c11377, some c11256, some c11433, some c11422, some c4753, some c4773, some c4760, some c4761, some c4750, some c4772, some c4758, some c11434, some c3603, some c3850, some c4801, some c3756, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11435 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11435 : lratChecker f11435 p11435 = .success := by decide +kernel
theorem unsat11435 : Unsatisfiable (PosFin 65) f11435 := by
  apply lratCheckerSound f11435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11435
  · intro a ha; simp [p11435] at ha; subst a; trivial
  · exact checked11435
theorem derived11435 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11435 := by
  apply localUnsat_implies_entails f11435 [c11402, c11170, c11377, c11256, c11433, c11422, c4753, c4773, c4760, c4761, c4750, c4772, c4758, c11434, c3603, c3850, c4801, c3756] c11435 unsat11435 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11377 := derived11377 a h
  have h3 : Entails.eval a c11256 := derived11256 a h
  have h4 : Entails.eval a c11433 := derived11433 a h
  have h5 : Entails.eval a c11422 := derived11422 a h
  have h6 : Entails.eval a c4753 := h 4752 (by decide)
  have h7 : Entails.eval a c4773 := h 4772 (by decide)
  have h8 : Entails.eval a c4760 := h 4759 (by decide)
  have h9 : Entails.eval a c4761 := h 4760 (by decide)
  have h10 : Entails.eval a c4750 := h 4749 (by decide)
  have h11 : Entails.eval a c4772 := h 4771 (by decide)
  have h12 : Entails.eval a c4758 := h 4757 (by decide)
  have h13 : Entails.eval a c11434 := derived11434 a h
  have h14 : Entails.eval a c3603 := h 3602 (by decide)
  have h15 : Entails.eval a c3850 := h 3849 (by decide)
  have h16 : Entails.eval a c4801 := h 4800 (by decide)
  have h17 : Entails.eval a c3756 := h 3755 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11436 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11436 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c11433, some c11422, some c11435, some c4763, some c4749, some c4764, some c3603, some c4801, some c3753, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11436 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11436 : lratChecker f11436 p11436 = .success := by decide +kernel
theorem unsat11436 : Unsatisfiable (PosFin 65) f11436 := by
  apply lratCheckerSound f11436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11436
  · intro a ha; simp [p11436] at ha; subst a; trivial
  · exact checked11436
theorem derived11436 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11436 := by
  apply localUnsat_implies_entails f11436 [c11402, c11256, c11433, c11422, c11435, c4763, c4749, c4764, c3603, c4801, c3753] c11436 unsat11436 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11433 := derived11433 a h
  have h3 : Entails.eval a c11422 := derived11422 a h
  have h4 : Entails.eval a c11435 := derived11435 a h
  have h5 : Entails.eval a c4763 := h 4762 (by decide)
  have h6 : Entails.eval a c4749 := h 4748 (by decide)
  have h7 : Entails.eval a c4764 := h 4763 (by decide)
  have h8 : Entails.eval a c3603 := h 3602 (by decide)
  have h9 : Entails.eval a c4801 := h 4800 (by decide)
  have h10 : Entails.eval a c3753 := h 3752 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11437 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11437 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11402, some c11436, some c11433, some c11422, some c11435, some c4763, some c4749, some c4764, some c3752, some c3761, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11437 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11437 : lratChecker f11437 p11437 = .success := by decide +kernel
theorem unsat11437 : Unsatisfiable (PosFin 65) f11437 := by
  apply lratCheckerSound f11437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11437
  · intro a ha; simp [p11437] at ha; subst a; trivial
  · exact checked11437
theorem derived11437 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11437 := by
  apply localUnsat_implies_entails f11437 [c11256, c11402, c11436, c11433, c11422, c11435, c4763, c4749, c4764, c3752, c3761] c11437 unsat11437 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11436 := derived11436 a h
  have h3 : Entails.eval a c11433 := derived11433 a h
  have h4 : Entails.eval a c11422 := derived11422 a h
  have h5 : Entails.eval a c11435 := derived11435 a h
  have h6 : Entails.eval a c4763 := h 4762 (by decide)
  have h7 : Entails.eval a c4749 := h 4748 (by decide)
  have h8 : Entails.eval a c4764 := h 4763 (by decide)
  have h9 : Entails.eval a c3752 := h 3751 (by decide)
  have h10 : Entails.eval a c3761 := h 3760 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11438 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11438 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c11436, some c11433, some c11422, some c11435, some c4763, some c4764, some c4760, some c4749, some c11437, some c3605, some c3601, some c3606, some c11418, some c10492, some c4848, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11438 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11438 : lratChecker f11438 p11438 = .success := by decide +kernel
theorem unsat11438 : Unsatisfiable (PosFin 65) f11438 := by
  apply lratCheckerSound f11438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11438
  · intro a ha; simp [p11438] at ha; subst a; trivial
  · exact checked11438
theorem derived11438 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11438 := by
  apply localUnsat_implies_entails f11438 [c11402, c11256, c11436, c11433, c11422, c11435, c4763, c4764, c4760, c4749, c11437, c3605, c3601, c3606, c11418, c10492, c4848] c11438 unsat11438 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11436 := derived11436 a h
  have h3 : Entails.eval a c11433 := derived11433 a h
  have h4 : Entails.eval a c11422 := derived11422 a h
  have h5 : Entails.eval a c11435 := derived11435 a h
  have h6 : Entails.eval a c4763 := h 4762 (by decide)
  have h7 : Entails.eval a c4764 := h 4763 (by decide)
  have h8 : Entails.eval a c4760 := h 4759 (by decide)
  have h9 : Entails.eval a c4749 := h 4748 (by decide)
  have h10 : Entails.eval a c11437 := derived11437 a h
  have h11 : Entails.eval a c3605 := h 3604 (by decide)
  have h12 : Entails.eval a c3601 := h 3600 (by decide)
  have h13 : Entails.eval a c3606 := h 3605 (by decide)
  have h14 : Entails.eval a c11418 := derived11418 a h
  have h15 : Entails.eval a c10492 := derived10492 a h
  have h16 : Entails.eval a c4848 := h 4847 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11439 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11439 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11377, some c11256, some c11402, some c11170, some c11331, some c11433, some c11422, some c11435, some c4763, some c4749, some c4764, some c11438, some c4320, some c4326, some c4770, some c11430, some c3076, some c3321, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11439 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11439 : lratChecker f11439 p11439 = .success := by decide +kernel
theorem unsat11439 : Unsatisfiable (PosFin 65) f11439 := by
  apply lratCheckerSound f11439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11439
  · intro a ha; simp [p11439] at ha; subst a; trivial
  · exact checked11439
theorem derived11439 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11439 := by
  apply localUnsat_implies_entails f11439 [c11377, c11256, c11402, c11170, c11331, c11433, c11422, c11435, c4763, c4749, c4764, c11438, c4320, c4326, c4770, c11430, c3076, c3321] c11439 unsat11439 (by rfl) a
  have h0 : Entails.eval a c11377 := derived11377 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c11170 := derived11170 a h
  have h4 : Entails.eval a c11331 := derived11331 a h
  have h5 : Entails.eval a c11433 := derived11433 a h
  have h6 : Entails.eval a c11422 := derived11422 a h
  have h7 : Entails.eval a c11435 := derived11435 a h
  have h8 : Entails.eval a c4763 := h 4762 (by decide)
  have h9 : Entails.eval a c4749 := h 4748 (by decide)
  have h10 : Entails.eval a c4764 := h 4763 (by decide)
  have h11 : Entails.eval a c11438 := derived11438 a h
  have h12 : Entails.eval a c4320 := h 4319 (by decide)
  have h13 : Entails.eval a c4326 := h 4325 (by decide)
  have h14 : Entails.eval a c4770 := h 4769 (by decide)
  have h15 : Entails.eval a c11430 := derived11430 a h
  have h16 : Entails.eval a c3076 := h 3075 (by decide)
  have h17 : Entails.eval a c3321 := h 3320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11440 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨26, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11440 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11170, some c11256, some c4764, some c4749, some c11439, some c5058, some c4144, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p11440 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11440 : lratChecker f11440 p11440 = .success := by decide +kernel
theorem unsat11440 : Unsatisfiable (PosFin 65) f11440 := by
  apply lratCheckerSound f11440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11440
  · intro a ha; simp [p11440] at ha; subst a; trivial
  · exact checked11440
theorem derived11440 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11440 := by
  apply localUnsat_implies_entails f11440 [c11402, c11170, c11256, c4764, c4749, c11439, c5058, c4144] c11440 unsat11440 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11256 := derived11256 a h
  have h3 : Entails.eval a c4764 := h 4763 (by decide)
  have h4 : Entails.eval a c4749 := h 4748 (by decide)
  have h5 : Entails.eval a c11439 := derived11439 a h
  have h6 : Entails.eval a c5058 := h 5057 (by decide)
  have h7 : Entails.eval a c4144 := h 4143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11441 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11441 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c11422, some c11433, some c11435, some c4763, some c11440, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p11441 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11441 : lratChecker f11441 p11441 = .success := by decide +kernel
theorem unsat11441 : Unsatisfiable (PosFin 65) f11441 := by
  apply lratCheckerSound f11441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11441
  · intro a ha; simp [p11441] at ha; subst a; trivial
  · exact checked11441
theorem derived11441 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11441 := by
  apply localUnsat_implies_entails f11441 [c11402, c11256, c11422, c11433, c11435, c4763, c11440] c11441 unsat11441 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11422 := derived11422 a h
  have h3 : Entails.eval a c11433 := derived11433 a h
  have h4 : Entails.eval a c11435 := derived11435 a h
  have h5 : Entails.eval a c4763 := h 4762 (by decide)
  have h6 : Entails.eval a c11440 := derived11440 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11442 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11442 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c11170, some c11377, some c5052, some c5054, some c3848, some c5061, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11442 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11442 : lratChecker f11442 p11442 = .success := by decide +kernel
theorem unsat11442 : Unsatisfiable (PosFin 65) f11442 := by
  apply lratCheckerSound f11442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11442
  · intro a ha; simp [p11442] at ha; subst a; trivial
  · exact checked11442
theorem derived11442 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11442 := by
  apply localUnsat_implies_entails f11442 [c11402, c11256, c11170, c11377, c5052, c5054, c3848, c5061] c11442 unsat11442 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11377 := derived11377 a h
  have h4 : Entails.eval a c5052 := h 5051 (by decide)
  have h5 : Entails.eval a c5054 := h 5053 (by decide)
  have h6 : Entails.eval a c3848 := h 3847 (by decide)
  have h7 : Entails.eval a c5061 := h 5060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11443 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11443 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11441, some c11402, some c11256, some c5063, some c5061, some c4152, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11443 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11443 : lratChecker f11443 p11443 = .success := by decide +kernel
theorem unsat11443 : Unsatisfiable (PosFin 65) f11443 := by
  apply lratCheckerSound f11443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11443
  · intro a ha; simp [p11443] at ha; subst a; trivial
  · exact checked11443
theorem derived11443 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11443 := by
  apply localUnsat_implies_entails f11443 [c11170, c11441, c11402, c11256, c5063, c5061, c4152] c11443 unsat11443 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11441 := derived11441 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c11256 := derived11256 a h
  have h4 : Entails.eval a c5063 := h 5062 (by decide)
  have h5 : Entails.eval a c5061 := h 5060 (by decide)
  have h6 : Entails.eval a c4152 := h 4151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11444 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨29, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11444 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11402, some c11170, some c11377, some c3861, some c5067, some c4153, some c5066, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11444 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11444 : lratChecker f11444 p11444 = .success := by decide +kernel
theorem unsat11444 : Unsatisfiable (PosFin 65) f11444 := by
  apply lratCheckerSound f11444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11444
  · intro a ha; simp [p11444] at ha; subst a; trivial
  · exact checked11444
theorem derived11444 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11444 := by
  apply localUnsat_implies_entails f11444 [c11256, c11402, c11170, c11377, c3861, c5067, c4153, c5066] c11444 unsat11444 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11377 := derived11377 a h
  have h4 : Entails.eval a c3861 := h 3860 (by decide)
  have h5 : Entails.eval a c5067 := h 5066 (by decide)
  have h6 : Entails.eval a c4153 := h 4152 (by decide)
  have h7 : Entails.eval a c5066 := h 5065 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11445 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11445 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11402, some c11443, some c5053, some c11444, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11445 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11445 : lratChecker f11445 p11445 = .success := by decide +kernel
theorem unsat11445 : Unsatisfiable (PosFin 65) f11445 := by
  apply lratCheckerSound f11445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11445
  · intro a ha; simp [p11445] at ha; subst a; trivial
  · exact checked11445
theorem derived11445 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11445 := by
  apply localUnsat_implies_entails f11445 [c11256, c11402, c11443, c5053, c11444] c11445 unsat11445 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11443 := derived11443 a h
  have h3 : Entails.eval a c5053 := h 5052 (by decide)
  have h4 : Entails.eval a c11444 := derived11444 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11446 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11446 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11377, some c11402, some c11442, some c11445, some c4145, some c3850, some c3859, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11446 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11446 : lratChecker f11446 p11446 = .success := by decide +kernel
theorem unsat11446 : Unsatisfiable (PosFin 65) f11446 := by
  apply lratCheckerSound f11446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11446
  · intro a ha; simp [p11446] at ha; subst a; trivial
  · exact checked11446
theorem derived11446 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11446 := by
  apply localUnsat_implies_entails f11446 [c11170, c11377, c11402, c11442, c11445, c4145, c3850, c3859] c11446 unsat11446 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c11442 := derived11442 a h
  have h4 : Entails.eval a c11445 := derived11445 a h
  have h5 : Entails.eval a c4145 := h 4144 (by decide)
  have h6 : Entails.eval a c3850 := h 3849 (by decide)
  have h7 : Entails.eval a c3859 := h 3858 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11447 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨23, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11447 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11377, some c11402, some c3855, some c3859, some c4151, some c3857, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11447 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11447 : lratChecker f11447 p11447 = .success := by decide +kernel
theorem unsat11447 : Unsatisfiable (PosFin 65) f11447 := by
  apply lratCheckerSound f11447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11447
  · intro a ha; simp [p11447] at ha; subst a; trivial
  · exact checked11447
theorem derived11447 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11447 := by
  apply localUnsat_implies_entails f11447 [c11170, c11377, c11402, c3855, c3859, c4151, c3857] c11447 unsat11447 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11377 := derived11377 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c3855 := h 3854 (by decide)
  have h4 : Entails.eval a c3859 := h 3858 (by decide)
  have h5 : Entails.eval a c4151 := h 4150 (by decide)
  have h6 : Entails.eval a c3857 := h 3856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11448 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11448 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11377, some c11170, some c11441, some c11402, some c11256, some c11446, some c11447, some c3853, some c4143, some c4142, some c5057, some c5066, some c5062, some c11390, some c11380, some c5049, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11448 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11448 : lratChecker f11448 p11448 = .success := by decide +kernel
theorem unsat11448 : Unsatisfiable (PosFin 65) f11448 := by
  apply lratCheckerSound f11448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11448
  · intro a ha; simp [p11448] at ha; subst a; trivial
  · exact checked11448
theorem derived11448 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11448 := by
  apply localUnsat_implies_entails f11448 [c11377, c11170, c11441, c11402, c11256, c11446, c11447, c3853, c4143, c4142, c5057, c5066, c5062, c11390, c11380, c5049] c11448 unsat11448 (by rfl) a
  have h0 : Entails.eval a c11377 := derived11377 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11441 := derived11441 a h
  have h3 : Entails.eval a c11402 := derived11402 a h
  have h4 : Entails.eval a c11256 := derived11256 a h
  have h5 : Entails.eval a c11446 := derived11446 a h
  have h6 : Entails.eval a c11447 := derived11447 a h
  have h7 : Entails.eval a c3853 := h 3852 (by decide)
  have h8 : Entails.eval a c4143 := h 4142 (by decide)
  have h9 : Entails.eval a c4142 := h 4141 (by decide)
  have h10 : Entails.eval a c5057 := h 5056 (by decide)
  have h11 : Entails.eval a c5066 := h 5065 (by decide)
  have h12 : Entails.eval a c5062 := h 5061 (by decide)
  have h13 : Entails.eval a c11390 := derived11390 a h
  have h14 : Entails.eval a c11380 := derived11380 a h
  have h15 : Entails.eval a c5049 := h 5048 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11449 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11449 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11441, some c11377, some c11402, some c11170, some c11448, some c11446, some c4141, some c3858, some c5060, some c5056, some c4149, some c3852, some c4148, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11449 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11449 : lratChecker f11449 p11449 = .success := by decide +kernel
theorem unsat11449 : Unsatisfiable (PosFin 65) f11449 := by
  apply lratCheckerSound f11449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11449
  · intro a ha; simp [p11449] at ha; subst a; trivial
  · exact checked11449
theorem derived11449 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11449 := by
  apply localUnsat_implies_entails f11449 [c11256, c11441, c11377, c11402, c11170, c11448, c11446, c4141, c3858, c5060, c5056, c4149, c3852, c4148] c11449 unsat11449 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11441 := derived11441 a h
  have h2 : Entails.eval a c11377 := derived11377 a h
  have h3 : Entails.eval a c11402 := derived11402 a h
  have h4 : Entails.eval a c11170 := derived11170 a h
  have h5 : Entails.eval a c11448 := derived11448 a h
  have h6 : Entails.eval a c11446 := derived11446 a h
  have h7 : Entails.eval a c4141 := h 4140 (by decide)
  have h8 : Entails.eval a c3858 := h 3857 (by decide)
  have h9 : Entails.eval a c5060 := h 5059 (by decide)
  have h10 : Entails.eval a c5056 := h 5055 (by decide)
  have h11 : Entails.eval a c4149 := h 4148 (by decide)
  have h12 : Entails.eval a c3852 := h 3851 (by decide)
  have h13 : Entails.eval a c4148 := h 4147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11450 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11450 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11441, some c11256, some c11170, some c4146, some c5055, some c11443, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11450 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11450 : lratChecker f11450 p11450 = .success := by decide +kernel
theorem unsat11450 : Unsatisfiable (PosFin 65) f11450 := by
  apply lratCheckerSound f11450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11450
  · intro a ha; simp [p11450] at ha; subst a; trivial
  · exact checked11450
theorem derived11450 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11450 := by
  apply localUnsat_implies_entails f11450 [c11402, c11441, c11256, c11170, c4146, c5055, c11443] c11450 unsat11450 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11441 := derived11441 a h
  have h2 : Entails.eval a c11256 := derived11256 a h
  have h3 : Entails.eval a c11170 := derived11170 a h
  have h4 : Entails.eval a c4146 := h 4145 (by decide)
  have h5 : Entails.eval a c5055 := h 5054 (by decide)
  have h6 : Entails.eval a c11443 := derived11443 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived11450

end CochromaticTwenty.Certificates.FixedCore0
