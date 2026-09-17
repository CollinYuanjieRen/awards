import MerLeanExperiment.Certificates.FixedCore1.Steps3300_3399

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9281 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9281 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9262, some c9260, some c9265, some c6969, some c7038, some c7016, some c6845, some c6857, some c9280, some c9080, some c6993, some c6822, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9281 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9281 : lratChecker f9281 p9281 = .success := by decide +kernel
theorem unsat9281 : Unsatisfiable (PosFin 65) f9281 := by
  apply lratCheckerSound f9281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9281
  · intro a ha; simp [p9281] at ha; subst a; trivial
  · exact checked9281
theorem derived9281 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9281 := by
  apply localUnsat_implies_entails f9281 [c9229, c9262, c9260, c9265, c6969, c7038, c7016, c6845, c6857, c9280, c9080, c6993, c6822] c9281 unsat9281 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9262 := derived9262 a h
  have h2 : Entails.eval a c9260 := derived9260 a h
  have h3 : Entails.eval a c9265 := derived9265 a h
  have h4 : Entails.eval a c6969 := derived6969 a h
  have h5 : Entails.eval a c7038 := derived7038 a h
  have h6 : Entails.eval a c7016 := derived7016 a h
  have h7 : Entails.eval a c6845 := derived6845 a h
  have h8 : Entails.eval a c6857 := derived6857 a h
  have h9 : Entails.eval a c9280 := derived9280 a h
  have h10 : Entails.eval a c9080 := derived9080 a h
  have h11 : Entails.eval a c6993 := derived6993 a h
  have h12 : Entails.eval a c6822 := derived6822 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9282 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨49, by decide⟩, false), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9282 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9281, some c9262, some c9260, some c7038, some c7016, some c6845, some c5001, some c6993, some c6822, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9282 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9282 : lratChecker f9282 p9282 = .success := by decide +kernel
theorem unsat9282 : Unsatisfiable (PosFin 65) f9282 := by
  apply lratCheckerSound f9282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9282
  · intro a ha; simp [p9282] at ha; subst a; trivial
  · exact checked9282
theorem derived9282 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9282 := by
  apply localUnsat_implies_entails f9282 [c9229, c9281, c9262, c9260, c7038, c7016, c6845, c5001, c6993, c6822] c9282 unsat9282 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9281 := derived9281 a h
  have h2 : Entails.eval a c9262 := derived9262 a h
  have h3 : Entails.eval a c9260 := derived9260 a h
  have h4 : Entails.eval a c7038 := derived7038 a h
  have h5 : Entails.eval a c7016 := derived7016 a h
  have h6 : Entails.eval a c6845 := derived6845 a h
  have h7 : Entails.eval a c5001 := h 5000 (by decide)
  have h8 : Entails.eval a c6993 := derived6993 a h
  have h9 : Entails.eval a c6822 := derived6822 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9283 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9283 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c9281, some c9262, some c9282, some c6969, some c6977, some c5135, some c5137, some c5134, some c5237, some c5147, some c4184, some c5148, some c5141, some c6845, some c4285, some c4221, some c4453, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9283 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9283 : lratChecker f9283 p9283 = .success := by decide +kernel
theorem unsat9283 : Unsatisfiable (PosFin 65) f9283 := by
  apply lratCheckerSound f9283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9283
  · intro a ha; simp [p9283] at ha; subst a; trivial
  · exact checked9283
theorem derived9283 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9283 := by
  apply localUnsat_implies_entails f9283 [c9229, c9228, c9281, c9262, c9282, c6969, c6977, c5135, c5137, c5134, c5237, c5147, c4184, c5148, c5141, c6845, c4285, c4221, c4453] c9283 unsat9283 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9281 := derived9281 a h
  have h3 : Entails.eval a c9262 := derived9262 a h
  have h4 : Entails.eval a c9282 := derived9282 a h
  have h5 : Entails.eval a c6969 := derived6969 a h
  have h6 : Entails.eval a c6977 := derived6977 a h
  have h7 : Entails.eval a c5135 := h 5134 (by decide)
  have h8 : Entails.eval a c5137 := h 5136 (by decide)
  have h9 : Entails.eval a c5134 := h 5133 (by decide)
  have h10 : Entails.eval a c5237 := h 5236 (by decide)
  have h11 : Entails.eval a c5147 := h 5146 (by decide)
  have h12 : Entails.eval a c4184 := h 4183 (by decide)
  have h13 : Entails.eval a c5148 := h 5147 (by decide)
  have h14 : Entails.eval a c5141 := h 5140 (by decide)
  have h15 : Entails.eval a c6845 := derived6845 a h
  have h16 : Entails.eval a c4285 := h 4284 (by decide)
  have h17 : Entails.eval a c4221 := h 4220 (by decide)
  have h18 : Entails.eval a c4453 := h 4452 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9284 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9284 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9260, some c9281, some c9283, some c6975, some c6957, some c7013, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9284 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9284 : lratChecker f9284 p9284 = .success := by decide +kernel
theorem unsat9284 : Unsatisfiable (PosFin 65) f9284 := by
  apply lratCheckerSound f9284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9284
  · intro a ha; simp [p9284] at ha; subst a; trivial
  · exact checked9284
theorem derived9284 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9284 := by
  apply localUnsat_implies_entails f9284 [c9260, c9281, c9283, c6975, c6957, c7013] c9284 unsat9284 (by rfl) a
  have h0 : Entails.eval a c9260 := derived9260 a h
  have h1 : Entails.eval a c9281 := derived9281 a h
  have h2 : Entails.eval a c9283 := derived9283 a h
  have h3 : Entails.eval a c6975 := derived6975 a h
  have h4 : Entails.eval a c6957 := derived6957 a h
  have h5 : Entails.eval a c7013 := derived7013 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9285 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9285 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6927, some c7018, some c6884, some c6943, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9285 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9285 : lratChecker f9285 p9285 = .success := by decide +kernel
theorem unsat9285 : Unsatisfiable (PosFin 65) f9285 := by
  apply lratCheckerSound f9285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9285
  · intro a ha; simp [p9285] at ha; subst a; trivial
  · exact checked9285
theorem derived9285 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9285 := by
  apply localUnsat_implies_entails f9285 [c6927, c7018, c6884, c6943] c9285 unsat9285 (by rfl) a
  have h0 : Entails.eval a c6927 := derived6927 a h
  have h1 : Entails.eval a c7018 := derived7018 a h
  have h2 : Entails.eval a c6884 := derived6884 a h
  have h3 : Entails.eval a c6943 := derived6943 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9286 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9286 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9284, some c9260, some c9285, some c6957, some c6894, some c6891, some c6844, some c6853, some c9267, some c4971, some c3964, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9286 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9286 : lratChecker f9286 p9286 = .success := by decide +kernel
theorem unsat9286 : Unsatisfiable (PosFin 65) f9286 := by
  apply lratCheckerSound f9286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9286
  · intro a ha; simp [p9286] at ha; subst a; trivial
  · exact checked9286
theorem derived9286 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9286 := by
  apply localUnsat_implies_entails f9286 [c9229, c9284, c9260, c9285, c6957, c6894, c6891, c6844, c6853, c9267, c4971, c3964] c9286 unsat9286 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9284 := derived9284 a h
  have h2 : Entails.eval a c9260 := derived9260 a h
  have h3 : Entails.eval a c9285 := derived9285 a h
  have h4 : Entails.eval a c6957 := derived6957 a h
  have h5 : Entails.eval a c6894 := derived6894 a h
  have h6 : Entails.eval a c6891 := derived6891 a h
  have h7 : Entails.eval a c6844 := derived6844 a h
  have h8 : Entails.eval a c6853 := derived6853 a h
  have h9 : Entails.eval a c9267 := derived9267 a h
  have h10 : Entails.eval a c4971 := h 4970 (by decide)
  have h11 : Entails.eval a c3964 := h 3963 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9287 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨43, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9287 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c3954, some c4709, some c5397, some c3972, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p9287 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9287 : lratChecker f9287 p9287 = .success := by decide +kernel
theorem unsat9287 : Unsatisfiable (PosFin 65) f9287 := by
  apply lratCheckerSound f9287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9287
  · intro a ha; simp [p9287] at ha; subst a; trivial
  · exact checked9287
theorem derived9287 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9287 := by
  apply localUnsat_implies_entails f9287 [c9229, c3954, c4709, c5397, c3972] c9287 unsat9287 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c3954 := h 3953 (by decide)
  have h2 : Entails.eval a c4709 := h 4708 (by decide)
  have h3 : Entails.eval a c5397 := h 5396 (by decide)
  have h4 : Entails.eval a c3972 := h 3971 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9288 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨57, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9288 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c5505, some c4753, some c5529, some c4875, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p9288 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9288 : lratChecker f9288 p9288 = .success := by decide +kernel
theorem unsat9288 : Unsatisfiable (PosFin 65) f9288 := by
  apply lratCheckerSound f9288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9288
  · intro a ha; simp [p9288] at ha; subst a; trivial
  · exact checked9288
theorem derived9288 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9288 := by
  apply localUnsat_implies_entails f9288 [c9229, c5505, c4753, c5529, c4875] c9288 unsat9288 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c5505 := h 5504 (by decide)
  have h2 : Entails.eval a c4753 := h 4752 (by decide)
  have h3 : Entails.eval a c5529 := h 5528 (by decide)
  have h4 : Entails.eval a c4875 := h 4874 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9289 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9289 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9260, some c9284, some c9286, some c9287, some c4954, some c9288, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9289 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9289 : lratChecker f9289 p9289 = .success := by decide +kernel
theorem unsat9289 : Unsatisfiable (PosFin 65) f9289 := by
  apply lratCheckerSound f9289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9289
  · intro a ha; simp [p9289] at ha; subst a; trivial
  · exact checked9289
theorem derived9289 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9289 := by
  apply localUnsat_implies_entails f9289 [c9229, c9260, c9284, c9286, c9287, c4954, c9288] c9289 unsat9289 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9260 := derived9260 a h
  have h2 : Entails.eval a c9284 := derived9284 a h
  have h3 : Entails.eval a c9286 := derived9286 a h
  have h4 : Entails.eval a c9287 := derived9287 a h
  have h5 : Entails.eval a c4954 := h 4953 (by decide)
  have h6 : Entails.eval a c9288 := derived9288 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9290 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨39, by decide⟩, true), (⟨49, by decide⟩, false), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9290 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9288, some c7019, some c6929, some c6868, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9290 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9290 : lratChecker f9290 p9290 = .success := by decide +kernel
theorem unsat9290 : Unsatisfiable (PosFin 65) f9290 := by
  apply lratCheckerSound f9290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9290
  · intro a ha; simp [p9290] at ha; subst a; trivial
  · exact checked9290
theorem derived9290 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9290 := by
  apply localUnsat_implies_entails f9290 [c9288, c7019, c6929, c6868] c9290 unsat9290 (by rfl) a
  have h0 : Entails.eval a c9288 := derived9288 a h
  have h1 : Entails.eval a c7019 := derived7019 a h
  have h2 : Entails.eval a c6929 := derived6929 a h
  have h3 : Entails.eval a c6868 := derived6868 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9291 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨43, by decide⟩, false), (⟨39, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9291 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9289, some c6964, some c6789, some c6802, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9291 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9291 : lratChecker f9291 p9291 = .success := by decide +kernel
theorem unsat9291 : Unsatisfiable (PosFin 65) f9291 := by
  apply lratCheckerSound f9291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9291
  · intro a ha; simp [p9291] at ha; subst a; trivial
  · exact checked9291
theorem derived9291 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9291 := by
  apply localUnsat_implies_entails f9291 [c9289, c6964, c6789, c6802] c9291 unsat9291 (by rfl) a
  have h0 : Entails.eval a c9289 := derived9289 a h
  have h1 : Entails.eval a c6964 := derived6964 a h
  have h2 : Entails.eval a c6789 := derived6789 a h
  have h3 : Entails.eval a c6802 := derived6802 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9292 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨47, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, true), (⟨40, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9292 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c3780, some c3748, some c3923, some c3928, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9292 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9292 : lratChecker f9292 p9292 = .success := by decide +kernel
theorem unsat9292 : Unsatisfiable (PosFin 65) f9292 := by
  apply lratCheckerSound f9292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9292
  · intro a ha; simp [p9292] at ha; subst a; trivial
  · exact checked9292
theorem derived9292 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9292 := by
  apply localUnsat_implies_entails f9292 [c9228, c3780, c3748, c3923, c3928] c9292 unsat9292 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c3780 := h 3779 (by decide)
  have h2 : Entails.eval a c3748 := h 3747 (by decide)
  have h3 : Entails.eval a c3923 := h 3922 (by decide)
  have h4 : Entails.eval a c3928 := h 3927 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9293 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9293 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c9289, some c9290, some c9291, some c4476, some c4599, some c4731, some c4178, some c4337, some c3994, some c5862, some c9292, some c3431, some c3885, some c3512, some c3444, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9293 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9293 : lratChecker f9293 p9293 = .success := by decide +kernel
theorem unsat9293 : Unsatisfiable (PosFin 65) f9293 := by
  apply lratCheckerSound f9293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9293
  · intro a ha; simp [p9293] at ha; subst a; trivial
  · exact checked9293
theorem derived9293 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9293 := by
  apply localUnsat_implies_entails f9293 [c9229, c9228, c9289, c9290, c9291, c4476, c4599, c4731, c4178, c4337, c3994, c5862, c9292, c3431, c3885, c3512, c3444] c9293 unsat9293 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9289 := derived9289 a h
  have h3 : Entails.eval a c9290 := derived9290 a h
  have h4 : Entails.eval a c9291 := derived9291 a h
  have h5 : Entails.eval a c4476 := h 4475 (by decide)
  have h6 : Entails.eval a c4599 := h 4598 (by decide)
  have h7 : Entails.eval a c4731 := h 4730 (by decide)
  have h8 : Entails.eval a c4178 := h 4177 (by decide)
  have h9 : Entails.eval a c4337 := h 4336 (by decide)
  have h10 : Entails.eval a c3994 := h 3993 (by decide)
  have h11 : Entails.eval a c5862 := h 5861 (by decide)
  have h12 : Entails.eval a c9292 := derived9292 a h
  have h13 : Entails.eval a c3431 := h 3430 (by decide)
  have h14 : Entails.eval a c3885 := h 3884 (by decide)
  have h15 : Entails.eval a c3512 := h 3511 (by decide)
  have h16 : Entails.eval a c3444 := h 3443 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9294 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨47, by decide⟩, true), (⟨57, by decide⟩, false), (⟨43, by decide⟩, false), (⟨49, by decide⟩, false), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9294 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c4476, some c6788, some c3568, some c5646, some c3545, some c3540, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9294 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9294 : lratChecker f9294 p9294 = .success := by decide +kernel
theorem unsat9294 : Unsatisfiable (PosFin 65) f9294 := by
  apply lratCheckerSound f9294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9294
  · intro a ha; simp [p9294] at ha; subst a; trivial
  · exact checked9294
theorem derived9294 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9294 := by
  apply localUnsat_implies_entails f9294 [c9229, c9228, c4476, c6788, c3568, c5646, c3545, c3540] c9294 unsat9294 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c4476 := h 4475 (by decide)
  have h3 : Entails.eval a c6788 := derived6788 a h
  have h4 : Entails.eval a c3568 := h 3567 (by decide)
  have h5 : Entails.eval a c5646 := h 5645 (by decide)
  have h6 : Entails.eval a c3545 := h 3544 (by decide)
  have h7 : Entails.eval a c3540 := h 3539 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9295 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨43, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9295 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c9293, some c9289, some c4476, some c4599, some c4954, some c4178, some c4132, some c9294, some c3780, some c3758, some c3669, some c3756, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9295 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9295 : lratChecker f9295 p9295 = .success := by decide +kernel
theorem unsat9295 : Unsatisfiable (PosFin 65) f9295 := by
  apply lratCheckerSound f9295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9295
  · intro a ha; simp [p9295] at ha; subst a; trivial
  · exact checked9295
theorem derived9295 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9295 := by
  apply localUnsat_implies_entails f9295 [c9229, c9228, c9293, c9289, c4476, c4599, c4954, c4178, c4132, c9294, c3780, c3758, c3669, c3756] c9295 unsat9295 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9293 := derived9293 a h
  have h3 : Entails.eval a c9289 := derived9289 a h
  have h4 : Entails.eval a c4476 := h 4475 (by decide)
  have h5 : Entails.eval a c4599 := h 4598 (by decide)
  have h6 : Entails.eval a c4954 := h 4953 (by decide)
  have h7 : Entails.eval a c4178 := h 4177 (by decide)
  have h8 : Entails.eval a c4132 := h 4131 (by decide)
  have h9 : Entails.eval a c9294 := derived9294 a h
  have h10 : Entails.eval a c3780 := h 3779 (by decide)
  have h11 : Entails.eval a c3758 := h 3757 (by decide)
  have h12 : Entails.eval a c3669 := h 3668 (by decide)
  have h13 : Entails.eval a c3756 := h 3755 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9296 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨46, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨57, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9296 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c4175, some c3913, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9296 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9296 : lratChecker f9296 p9296 = .success := by decide +kernel
theorem unsat9296 : Unsatisfiable (PosFin 65) f9296 := by
  apply lratCheckerSound f9296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9296
  · intro a ha; simp [p9296] at ha; subst a; trivial
  · exact checked9296
theorem derived9296 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9296 := by
  apply localUnsat_implies_entails f9296 [c9229, c4175, c3913] c9296 unsat9296 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c4175 := h 4174 (by decide)
  have h2 : Entails.eval a c3913 := h 3912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9297 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9297 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9293, some c9289, some c9295, some c6964, some c6789, some c6807, some c6845, some c6850, some c6901, some c9296, some c5182, some c5022, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9297 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9297 : lratChecker f9297 p9297 = .success := by decide +kernel
theorem unsat9297 : Unsatisfiable (PosFin 65) f9297 := by
  apply lratCheckerSound f9297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9297
  · intro a ha; simp [p9297] at ha; subst a; trivial
  · exact checked9297
theorem derived9297 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9297 := by
  apply localUnsat_implies_entails f9297 [c9229, c9293, c9289, c9295, c6964, c6789, c6807, c6845, c6850, c6901, c9296, c5182, c5022] c9297 unsat9297 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9293 := derived9293 a h
  have h2 : Entails.eval a c9289 := derived9289 a h
  have h3 : Entails.eval a c9295 := derived9295 a h
  have h4 : Entails.eval a c6964 := derived6964 a h
  have h5 : Entails.eval a c6789 := derived6789 a h
  have h6 : Entails.eval a c6807 := derived6807 a h
  have h7 : Entails.eval a c6845 := derived6845 a h
  have h8 : Entails.eval a c6850 := derived6850 a h
  have h9 : Entails.eval a c6901 := derived6901 a h
  have h10 : Entails.eval a c9296 := derived9296 a h
  have h11 : Entails.eval a c5182 := h 5181 (by decide)
  have h12 : Entails.eval a c5022 := h 5021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9298 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨57, by decide⟩, true), (⟨43, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9298 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6854, some c6857, some c6901, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9298 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9298 : lratChecker f9298 p9298 = .success := by decide +kernel
theorem unsat9298 : Unsatisfiable (PosFin 65) f9298 := by
  apply lratCheckerSound f9298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9298
  · intro a ha; simp [p9298] at ha; subst a; trivial
  · exact checked9298
theorem derived9298 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9298 := by
  apply localUnsat_implies_entails f9298 [c6854, c6857, c6901] c9298 unsat9298 (by rfl) a
  have h0 : Entails.eval a c6854 := derived6854 a h
  have h1 : Entails.eval a c6857 := derived6857 a h
  have h2 : Entails.eval a c6901 := derived6901 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9299 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨47, by decide⟩, true), (⟨57, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9299 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6807, some c7023, some c6784, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9299 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9299 : lratChecker f9299 p9299 = .success := by decide +kernel
theorem unsat9299 : Unsatisfiable (PosFin 65) f9299 := by
  apply lratCheckerSound f9299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9299
  · intro a ha; simp [p9299] at ha; subst a; trivial
  · exact checked9299
theorem derived9299 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9299 := by
  apply localUnsat_implies_entails f9299 [c6807, c7023, c6784] c9299 unsat9299 (by rfl) a
  have h0 : Entails.eval a c6807 := derived6807 a h
  have h1 : Entails.eval a c7023 := derived7023 a h
  have h2 : Entails.eval a c6784 := derived6784 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9300 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9300 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9297, some c9293, some c9289, some c9298, some c6845, some c9299, some c6969, some c7038, some c6815, some c6784, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9300 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9300 : lratChecker f9300 p9300 = .success := by decide +kernel
theorem unsat9300 : Unsatisfiable (PosFin 65) f9300 := by
  apply lratCheckerSound f9300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9300
  · intro a ha; simp [p9300] at ha; subst a; trivial
  · exact checked9300
theorem derived9300 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9300 := by
  apply localUnsat_implies_entails f9300 [c9297, c9293, c9289, c9298, c6845, c9299, c6969, c7038, c6815, c6784] c9300 unsat9300 (by rfl) a
  have h0 : Entails.eval a c9297 := derived9297 a h
  have h1 : Entails.eval a c9293 := derived9293 a h
  have h2 : Entails.eval a c9289 := derived9289 a h
  have h3 : Entails.eval a c9298 := derived9298 a h
  have h4 : Entails.eval a c6845 := derived6845 a h
  have h5 : Entails.eval a c9299 := derived9299 a h
  have h6 : Entails.eval a c6969 := derived6969 a h
  have h7 : Entails.eval a c7038 := derived7038 a h
  have h8 : Entails.eval a c6815 := derived6815 a h
  have h9 : Entails.eval a c6784 := derived6784 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9301 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9301 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c4709, some c5397, some c4069, some c3972, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p9301 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9301 : lratChecker f9301 p9301 = .success := by decide +kernel
theorem unsat9301 : Unsatisfiable (PosFin 65) f9301 := by
  apply lratCheckerSound f9301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9301
  · intro a ha; simp [p9301] at ha; subst a; trivial
  · exact checked9301
theorem derived9301 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9301 := by
  apply localUnsat_implies_entails f9301 [c9229, c4709, c5397, c4069, c3972] c9301 unsat9301 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c4709 := h 4708 (by decide)
  have h2 : Entails.eval a c5397 := h 5396 (by decide)
  have h3 : Entails.eval a c4069 := h 4068 (by decide)
  have h4 : Entails.eval a c3972 := h 3971 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9302 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9302 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9293, some c9297, some c9300, some c4954, some c9301, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9302 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9302 : lratChecker f9302 p9302 = .success := by decide +kernel
theorem unsat9302 : Unsatisfiable (PosFin 65) f9302 := by
  apply lratCheckerSound f9302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9302
  · intro a ha; simp [p9302] at ha; subst a; trivial
  · exact checked9302
theorem derived9302 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9302 := by
  apply localUnsat_implies_entails f9302 [c9229, c9293, c9297, c9300, c4954, c9301] c9302 unsat9302 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9293 := derived9293 a h
  have h2 : Entails.eval a c9297 := derived9297 a h
  have h3 : Entails.eval a c9300 := derived9300 a h
  have h4 : Entails.eval a c4954 := h 4953 (by decide)
  have h5 : Entails.eval a c9301 := derived9301 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9303 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨43, by decide⟩, true), (⟨57, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9303 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c7002, some c5421, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9303 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9303 : lratChecker f9303 p9303 = .success := by decide +kernel
theorem unsat9303 : Unsatisfiable (PosFin 65) f9303 := by
  apply lratCheckerSound f9303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9303
  · intro a ha; simp [p9303] at ha; subst a; trivial
  · exact checked9303
theorem derived9303 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9303 := by
  apply localUnsat_implies_entails f9303 [c9229, c7002, c5421] c9303 unsat9303 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c7002 := derived7002 a h
  have h2 : Entails.eval a c5421 := h 5420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9304 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9304 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6867, some c6824, some c6856, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9304 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9304 : lratChecker f9304 p9304 = .success := by decide +kernel
theorem unsat9304 : Unsatisfiable (PosFin 65) f9304 := by
  apply lratCheckerSound f9304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9304
  · intro a ha; simp [p9304] at ha; subst a; trivial
  · exact checked9304
theorem derived9304 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9304 := by
  apply localUnsat_implies_entails f9304 [c6867, c6824, c6856] c9304 unsat9304 (by rfl) a
  have h0 : Entails.eval a c6867 := derived6867 a h
  have h1 : Entails.eval a c6824 := derived6824 a h
  have h2 : Entails.eval a c6856 := derived6856 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9305 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9305 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9302, some c9289, some c6967, some c9304, some c6975, some c6932, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9305 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9305 : lratChecker f9305 p9305 = .success := by decide +kernel
theorem unsat9305 : Unsatisfiable (PosFin 65) f9305 := by
  apply lratCheckerSound f9305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9305
  · intro a ha; simp [p9305] at ha; subst a; trivial
  · exact checked9305
theorem derived9305 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9305 := by
  apply localUnsat_implies_entails f9305 [c9302, c9289, c6967, c9304, c6975, c6932] c9305 unsat9305 (by rfl) a
  have h0 : Entails.eval a c9302 := derived9302 a h
  have h1 : Entails.eval a c9289 := derived9289 a h
  have h2 : Entails.eval a c6967 := derived6967 a h
  have h3 : Entails.eval a c9304 := derived9304 a h
  have h4 : Entails.eval a c6975 := derived6975 a h
  have h5 : Entails.eval a c6932 := derived6932 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9306 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨57, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9306 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9302, some c9305, some c7013, some c9303, some c4971, some c6949, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9306 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9306 : lratChecker f9306 p9306 = .success := by decide +kernel
theorem unsat9306 : Unsatisfiable (PosFin 65) f9306 := by
  apply lratCheckerSound f9306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9306
  · intro a ha; simp [p9306] at ha; subst a; trivial
  · exact checked9306
theorem derived9306 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9306 := by
  apply localUnsat_implies_entails f9306 [c9229, c9302, c9305, c7013, c9303, c4971, c6949] c9306 unsat9306 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9302 := derived9302 a h
  have h2 : Entails.eval a c9305 := derived9305 a h
  have h3 : Entails.eval a c7013 := derived7013 a h
  have h4 : Entails.eval a c9303 := derived9303 a h
  have h5 : Entails.eval a c4971 := h 4970 (by decide)
  have h6 : Entails.eval a c6949 := derived6949 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9307 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨57, by decide⟩, false), (⟨49, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9307 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c4971, some c6949, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9307 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9307 : lratChecker f9307 p9307 = .success := by decide +kernel
theorem unsat9307 : Unsatisfiable (PosFin 65) f9307 := by
  apply lratCheckerSound f9307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9307
  · intro a ha; simp [p9307] at ha; subst a; trivial
  · exact checked9307
theorem derived9307 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9307 := by
  apply localUnsat_implies_entails f9307 [c9229, c4971, c6949] c9307 unsat9307 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c4971 := h 4970 (by decide)
  have h2 : Entails.eval a c6949 := derived6949 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9308 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨62, by decide⟩, true), (⟨36, by decide⟩, false), (⟨43, by decide⟩, false), (⟨57, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9308 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c3574, some c3512, some c3522, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p9308 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9308 : lratChecker f9308 p9308 = .success := by decide +kernel
theorem unsat9308 : Unsatisfiable (PosFin 65) f9308 := by
  apply lratCheckerSound f9308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9308
  · intro a ha; simp [p9308] at ha; subst a; trivial
  · exact checked9308
theorem derived9308 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9308 := by
  apply localUnsat_implies_entails f9308 [c9229, c9228, c3574, c3512, c3522] c9308 unsat9308 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c3574 := h 3573 (by decide)
  have h3 : Entails.eval a c3512 := h 3511 (by decide)
  have h4 : Entails.eval a c3522 := h 3521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9309 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨62, by decide⟩, true), (⟨38, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9309 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4598, some c5342, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p9309 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9309 : lratChecker f9309 p9309 = .success := by decide +kernel
theorem unsat9309 : Unsatisfiable (PosFin 65) f9309 := by
  apply lratCheckerSound f9309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9309
  · intro a ha; simp [p9309] at ha; subst a; trivial
  · exact checked9309
theorem derived9309 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9309 := by
  apply localUnsat_implies_entails f9309 [c4598, c5342] c9309 unsat9309 (by rfl) a
  have h0 : Entails.eval a c4598 := h 4597 (by decide)
  have h1 : Entails.eval a c5342 := h 5341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9310 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨38, by decide⟩, true), (⟨42, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨43, by decide⟩, false), (⟨57, by decide⟩, false), (⟨49, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9310 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c9308, some c9309, some c4586, some c3790, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p9310 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9310 : lratChecker f9310 p9310 = .success := by decide +kernel
theorem unsat9310 : Unsatisfiable (PosFin 65) f9310 := by
  apply lratCheckerSound f9310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9310
  · intro a ha; simp [p9310] at ha; subst a; trivial
  · exact checked9310
theorem derived9310 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9310 := by
  apply localUnsat_implies_entails f9310 [c9228, c9229, c9308, c9309, c4586, c3790] c9310 unsat9310 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9308 := derived9308 a h
  have h3 : Entails.eval a c9309 := derived9309 a h
  have h4 : Entails.eval a c4586 := h 4585 (by decide)
  have h5 : Entails.eval a c3790 := h 3789 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9311 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9311 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9302, some c9289, some c9306, some c6962, some c6972, some c6932, some c7021, some c6867, some c6826, some c7044, some c6848, some c7020, some c9307, some c9310, some c5900, some c3676, some c3524, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9311 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9311 : lratChecker f9311 p9311 = .success := by decide +kernel
theorem unsat9311 : Unsatisfiable (PosFin 65) f9311 := by
  apply lratCheckerSound f9311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9311
  · intro a ha; simp [p9311] at ha; subst a; trivial
  · exact checked9311
theorem derived9311 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9311 := by
  apply localUnsat_implies_entails f9311 [c9229, c9302, c9289, c9306, c6962, c6972, c6932, c7021, c6867, c6826, c7044, c6848, c7020, c9307, c9310, c5900, c3676, c3524] c9311 unsat9311 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9302 := derived9302 a h
  have h2 : Entails.eval a c9289 := derived9289 a h
  have h3 : Entails.eval a c9306 := derived9306 a h
  have h4 : Entails.eval a c6962 := derived6962 a h
  have h5 : Entails.eval a c6972 := derived6972 a h
  have h6 : Entails.eval a c6932 := derived6932 a h
  have h7 : Entails.eval a c7021 := derived7021 a h
  have h8 : Entails.eval a c6867 := derived6867 a h
  have h9 : Entails.eval a c6826 := derived6826 a h
  have h10 : Entails.eval a c7044 := derived7044 a h
  have h11 : Entails.eval a c6848 := derived6848 a h
  have h12 : Entails.eval a c7020 := derived7020 a h
  have h13 : Entails.eval a c9307 := derived9307 a h
  have h14 : Entails.eval a c9310 := derived9310 a h
  have h15 : Entails.eval a c5900 := derived5900 a h
  have h16 : Entails.eval a c3676 := h 3675 (by decide)
  have h17 : Entails.eval a c3524 := h 3523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9312 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨62, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9312 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9311, some c9302, some c9289, some c6962, some c6972, some c6789, some c9231, some c5630, some c3770, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9312 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9312 : lratChecker f9312 p9312 = .success := by decide +kernel
theorem unsat9312 : Unsatisfiable (PosFin 65) f9312 := by
  apply lratCheckerSound f9312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9312
  · intro a ha; simp [p9312] at ha; subst a; trivial
  · exact checked9312
theorem derived9312 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9312 := by
  apply localUnsat_implies_entails f9312 [c9229, c9311, c9302, c9289, c6962, c6972, c6789, c9231, c5630, c3770] c9312 unsat9312 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9311 := derived9311 a h
  have h2 : Entails.eval a c9302 := derived9302 a h
  have h3 : Entails.eval a c9289 := derived9289 a h
  have h4 : Entails.eval a c6962 := derived6962 a h
  have h5 : Entails.eval a c6972 := derived6972 a h
  have h6 : Entails.eval a c6789 := derived6789 a h
  have h7 : Entails.eval a c9231 := derived9231 a h
  have h8 : Entails.eval a c5630 := h 5629 (by decide)
  have h9 : Entails.eval a c3770 := h 3769 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9313 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9313 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9311, some c9289, some c9305, some c9298, some c7038, some c7016, some c6845, some c6784, some c6815, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9313 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9313 : lratChecker f9313 p9313 = .success := by decide +kernel
theorem unsat9313 : Unsatisfiable (PosFin 65) f9313 := by
  apply lratCheckerSound f9313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9313
  · intro a ha; simp [p9313] at ha; subst a; trivial
  · exact checked9313
theorem derived9313 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9313 := by
  apply localUnsat_implies_entails f9313 [c9311, c9289, c9305, c9298, c7038, c7016, c6845, c6784, c6815] c9313 unsat9313 (by rfl) a
  have h0 : Entails.eval a c9311 := derived9311 a h
  have h1 : Entails.eval a c9289 := derived9289 a h
  have h2 : Entails.eval a c9305 := derived9305 a h
  have h3 : Entails.eval a c9298 := derived9298 a h
  have h4 : Entails.eval a c7038 := derived7038 a h
  have h5 : Entails.eval a c7016 := derived7016 a h
  have h6 : Entails.eval a c6845 := derived6845 a h
  have h7 : Entails.eval a c6784 := derived6784 a h
  have h8 : Entails.eval a c6815 := derived6815 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9314 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨34, by decide⟩, true), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨43, by decide⟩, false), (⟨57, by decide⟩, true), (⟨49, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9314 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c6995, some c6801, some c6799, some c6800, some c3637, some c6292, some c4601, some c4179, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p9314 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9314 : lratChecker f9314 p9314 = .success := by decide +kernel
theorem unsat9314 : Unsatisfiable (PosFin 65) f9314 := by
  apply lratCheckerSound f9314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9314
  · intro a ha; simp [p9314] at ha; subst a; trivial
  · exact checked9314
theorem derived9314 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9314 := by
  apply localUnsat_implies_entails f9314 [c9228, c6995, c6801, c6799, c6800, c3637, c6292, c4601, c4179] c9314 unsat9314 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c6995 := derived6995 a h
  have h2 : Entails.eval a c6801 := derived6801 a h
  have h3 : Entails.eval a c6799 := derived6799 a h
  have h4 : Entails.eval a c6800 := derived6800 a h
  have h5 : Entails.eval a c3637 := h 3636 (by decide)
  have h6 : Entails.eval a c6292 := derived6292 a h
  have h7 : Entails.eval a c4601 := h 4600 (by decide)
  have h8 : Entails.eval a c4179 := h 4178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9315 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨63, by decide⟩, false), (⟨59, by decide⟩, false), (⟨48, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9315 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c2891, some c6713, some c2873, some c3139, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9315 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9315 : lratChecker f9315 p9315 = .success := by decide +kernel
theorem unsat9315 : Unsatisfiable (PosFin 65) f9315 := by
  apply lratCheckerSound f9315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9315
  · intro a ha; simp [p9315] at ha; subst a; trivial
  · exact checked9315
theorem derived9315 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9315 := by
  apply localUnsat_implies_entails f9315 [c9228, c2891, c6713, c2873, c3139] c9315 unsat9315 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c2891 := h 2890 (by decide)
  have h2 : Entails.eval a c6713 := derived6713 a h
  have h3 : Entails.eval a c2873 := h 2872 (by decide)
  have h4 : Entails.eval a c3139 := h 3138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9316 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨60, by decide⟩, true), (⟨56, by decide⟩, true), (⟨48, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, true), (⟨34, by decide⟩, true), (⟨36, by decide⟩, false), (⟨62, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9316 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3364, some c6758, some c6714, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9316 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9316 : lratChecker f9316 p9316 = .success := by decide +kernel
theorem unsat9316 : Unsatisfiable (PosFin 65) f9316 := by
  apply lratCheckerSound f9316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9316
  · intro a ha; simp [p9316] at ha; subst a; trivial
  · exact checked9316
theorem derived9316 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9316 := by
  apply localUnsat_implies_entails f9316 [c3364, c6758, c6714] c9316 unsat9316 (by rfl) a
  have h0 : Entails.eval a c3364 := h 3363 (by decide)
  have h1 : Entails.eval a c6758 := derived6758 a h
  have h2 : Entails.eval a c6714 := derived6714 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9317 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9317 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9289, some c9302, some c9311, some c9313, some c9291, some c6962, some c6789, some c9312, some c9299, some c6972, some c6932, some c6828, some c9314, some c6867, some c6849, some c6995, some c5957, some c5621, some c5344, some c5353, some c3660, some c4320, some c3677, some c9315, some c9316, some c6718, some c6717, some c6715, some c3302, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9317 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked9317 : lratChecker f9317 p9317 = .success := by decide +kernel
theorem unsat9317 : Unsatisfiable (PosFin 65) f9317 := by
  apply lratCheckerSound f9317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9317
  · intro a ha; simp [p9317] at ha; subst a; trivial
  · exact checked9317
theorem derived9317 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9317 := by
  apply localUnsat_implies_entails f9317 [c9228, c9289, c9302, c9311, c9313, c9291, c6962, c6789, c9312, c9299, c6972, c6932, c6828, c9314, c6867, c6849, c6995, c5957, c5621, c5344, c5353, c3660, c4320, c3677, c9315, c9316, c6718, c6717, c6715, c3302] c9317 unsat9317 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9289 := derived9289 a h
  have h2 : Entails.eval a c9302 := derived9302 a h
  have h3 : Entails.eval a c9311 := derived9311 a h
  have h4 : Entails.eval a c9313 := derived9313 a h
  have h5 : Entails.eval a c9291 := derived9291 a h
  have h6 : Entails.eval a c6962 := derived6962 a h
  have h7 : Entails.eval a c6789 := derived6789 a h
  have h8 : Entails.eval a c9312 := derived9312 a h
  have h9 : Entails.eval a c9299 := derived9299 a h
  have h10 : Entails.eval a c6972 := derived6972 a h
  have h11 : Entails.eval a c6932 := derived6932 a h
  have h12 : Entails.eval a c6828 := derived6828 a h
  have h13 : Entails.eval a c9314 := derived9314 a h
  have h14 : Entails.eval a c6867 := derived6867 a h
  have h15 : Entails.eval a c6849 := derived6849 a h
  have h16 : Entails.eval a c6995 := derived6995 a h
  have h17 : Entails.eval a c5957 := derived5957 a h
  have h18 : Entails.eval a c5621 := h 5620 (by decide)
  have h19 : Entails.eval a c5344 := h 5343 (by decide)
  have h20 : Entails.eval a c5353 := h 5352 (by decide)
  have h21 : Entails.eval a c3660 := h 3659 (by decide)
  have h22 : Entails.eval a c4320 := h 4319 (by decide)
  have h23 : Entails.eval a c3677 := h 3676 (by decide)
  have h24 : Entails.eval a c9315 := derived9315 a h
  have h25 : Entails.eval a c9316 := derived9316 a h
  have h26 : Entails.eval a c6718 := derived6718 a h
  have h27 : Entails.eval a c6717 := derived6717 a h
  have h28 : Entails.eval a c6715 := derived6715 a h
  have h29 : Entails.eval a c3302 := h 3301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9318 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9318 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9289, some c9302, some c9311, some c9313, some c6962, some c9299, some c6972, some c6932, some c9312, some c6828, some c6849, some c9291, some c6789, some c9314, some c9317, some c5836, some c5495, some c5254, some c6995, some c9309, some c4580, some c5182, some c5957, some c6718, some c6717, some c6715, some c3299, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9318 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked9318 : lratChecker f9318 p9318 = .success := by decide +kernel
theorem unsat9318 : Unsatisfiable (PosFin 65) f9318 := by
  apply lratCheckerSound f9318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9318
  · intro a ha; simp [p9318] at ha; subst a; trivial
  · exact checked9318
theorem derived9318 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9318 := by
  apply localUnsat_implies_entails f9318 [c9228, c9289, c9302, c9311, c9313, c6962, c9299, c6972, c6932, c9312, c6828, c6849, c9291, c6789, c9314, c9317, c5836, c5495, c5254, c6995, c9309, c4580, c5182, c5957, c6718, c6717, c6715, c3299] c9318 unsat9318 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9289 := derived9289 a h
  have h2 : Entails.eval a c9302 := derived9302 a h
  have h3 : Entails.eval a c9311 := derived9311 a h
  have h4 : Entails.eval a c9313 := derived9313 a h
  have h5 : Entails.eval a c6962 := derived6962 a h
  have h6 : Entails.eval a c9299 := derived9299 a h
  have h7 : Entails.eval a c6972 := derived6972 a h
  have h8 : Entails.eval a c6932 := derived6932 a h
  have h9 : Entails.eval a c9312 := derived9312 a h
  have h10 : Entails.eval a c6828 := derived6828 a h
  have h11 : Entails.eval a c6849 := derived6849 a h
  have h12 : Entails.eval a c9291 := derived9291 a h
  have h13 : Entails.eval a c6789 := derived6789 a h
  have h14 : Entails.eval a c9314 := derived9314 a h
  have h15 : Entails.eval a c9317 := derived9317 a h
  have h16 : Entails.eval a c5836 := h 5835 (by decide)
  have h17 : Entails.eval a c5495 := h 5494 (by decide)
  have h18 : Entails.eval a c5254 := h 5253 (by decide)
  have h19 : Entails.eval a c6995 := derived6995 a h
  have h20 : Entails.eval a c9309 := derived9309 a h
  have h21 : Entails.eval a c4580 := h 4579 (by decide)
  have h22 : Entails.eval a c5182 := h 5181 (by decide)
  have h23 : Entails.eval a c5957 := derived5957 a h
  have h24 : Entails.eval a c6718 := derived6718 a h
  have h25 : Entails.eval a c6717 := derived6717 a h
  have h26 : Entails.eval a c6715 := derived6715 a h
  have h27 : Entails.eval a c3299 := h 3298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9319 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9319 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9318, some c9302, some c9289, some c9311, some c9313, some c6962, some c9299, some c6972, some c6932, some c9312, some c6828, some c6849, some c9291, some c9317, some c5836, some c5495, some c6789, some c9314, some c3218, some c3374, some c3365, some c6763, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9319 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9319 : lratChecker f9319 p9319 = .success := by decide +kernel
theorem unsat9319 : Unsatisfiable (PosFin 65) f9319 := by
  apply lratCheckerSound f9319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9319
  · intro a ha; simp [p9319] at ha; subst a; trivial
  · exact checked9319
theorem derived9319 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9319 := by
  apply localUnsat_implies_entails f9319 [c9228, c9318, c9302, c9289, c9311, c9313, c6962, c9299, c6972, c6932, c9312, c6828, c6849, c9291, c9317, c5836, c5495, c6789, c9314, c3218, c3374, c3365, c6763] c9319 unsat9319 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9318 := derived9318 a h
  have h2 : Entails.eval a c9302 := derived9302 a h
  have h3 : Entails.eval a c9289 := derived9289 a h
  have h4 : Entails.eval a c9311 := derived9311 a h
  have h5 : Entails.eval a c9313 := derived9313 a h
  have h6 : Entails.eval a c6962 := derived6962 a h
  have h7 : Entails.eval a c9299 := derived9299 a h
  have h8 : Entails.eval a c6972 := derived6972 a h
  have h9 : Entails.eval a c6932 := derived6932 a h
  have h10 : Entails.eval a c9312 := derived9312 a h
  have h11 : Entails.eval a c6828 := derived6828 a h
  have h12 : Entails.eval a c6849 := derived6849 a h
  have h13 : Entails.eval a c9291 := derived9291 a h
  have h14 : Entails.eval a c9317 := derived9317 a h
  have h15 : Entails.eval a c5836 := h 5835 (by decide)
  have h16 : Entails.eval a c5495 := h 5494 (by decide)
  have h17 : Entails.eval a c6789 := derived6789 a h
  have h18 : Entails.eval a c9314 := derived9314 a h
  have h19 : Entails.eval a c3218 := h 3217 (by decide)
  have h20 : Entails.eval a c3374 := h 3373 (by decide)
  have h21 : Entails.eval a c3365 := h 3364 (by decide)
  have h22 : Entails.eval a c6763 := derived6763 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9320 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9320 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9289, some c9302, some c9311, some c9313, some c9291, some c6962, some c6972, some c6789, some c9312, some c6932, some c9299, some c6828, some c6995, some c6849, some c9309, some c9314, some c9317, some c5182, some c5836, some c5495, some c5254, some c4580, some c4937, some c9319, some c2866, some c6720, some c6716, some c6751, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9320 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked9320 : lratChecker f9320 p9320 = .success := by decide +kernel
theorem unsat9320 : Unsatisfiable (PosFin 65) f9320 := by
  apply lratCheckerSound f9320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9320
  · intro a ha; simp [p9320] at ha; subst a; trivial
  · exact checked9320
theorem derived9320 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9320 := by
  apply localUnsat_implies_entails f9320 [c9228, c9289, c9302, c9311, c9313, c9291, c6962, c6972, c6789, c9312, c6932, c9299, c6828, c6995, c6849, c9309, c9314, c9317, c5182, c5836, c5495, c5254, c4580, c4937, c9319, c2866, c6720, c6716, c6751] c9320 unsat9320 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9289 := derived9289 a h
  have h2 : Entails.eval a c9302 := derived9302 a h
  have h3 : Entails.eval a c9311 := derived9311 a h
  have h4 : Entails.eval a c9313 := derived9313 a h
  have h5 : Entails.eval a c9291 := derived9291 a h
  have h6 : Entails.eval a c6962 := derived6962 a h
  have h7 : Entails.eval a c6972 := derived6972 a h
  have h8 : Entails.eval a c6789 := derived6789 a h
  have h9 : Entails.eval a c9312 := derived9312 a h
  have h10 : Entails.eval a c6932 := derived6932 a h
  have h11 : Entails.eval a c9299 := derived9299 a h
  have h12 : Entails.eval a c6828 := derived6828 a h
  have h13 : Entails.eval a c6995 := derived6995 a h
  have h14 : Entails.eval a c6849 := derived6849 a h
  have h15 : Entails.eval a c9309 := derived9309 a h
  have h16 : Entails.eval a c9314 := derived9314 a h
  have h17 : Entails.eval a c9317 := derived9317 a h
  have h18 : Entails.eval a c5182 := h 5181 (by decide)
  have h19 : Entails.eval a c5836 := h 5835 (by decide)
  have h20 : Entails.eval a c5495 := h 5494 (by decide)
  have h21 : Entails.eval a c5254 := h 5253 (by decide)
  have h22 : Entails.eval a c4580 := h 4579 (by decide)
  have h23 : Entails.eval a c4937 := h 4936 (by decide)
  have h24 : Entails.eval a c9319 := derived9319 a h
  have h25 : Entails.eval a c2866 := h 2865 (by decide)
  have h26 : Entails.eval a c6720 := derived6720 a h
  have h27 : Entails.eval a c6716 := derived6716 a h
  have h28 : Entails.eval a c6751 := derived6751 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9321 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨36, by decide⟩, false), (⟨54, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9321 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c4371, some c4370, some c4365, some c4374, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p9321 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9321 : lratChecker f9321 p9321 = .success := by decide +kernel
theorem unsat9321 : Unsatisfiable (PosFin 65) f9321 := by
  apply lratCheckerSound f9321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9321
  · intro a ha; simp [p9321] at ha; subst a; trivial
  · exact checked9321
theorem derived9321 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9321 := by
  apply localUnsat_implies_entails f9321 [c9228, c9229, c4371, c4370, c4365, c4374] c9321 unsat9321 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c4371 := h 4370 (by decide)
  have h3 : Entails.eval a c4370 := h 4369 (by decide)
  have h4 : Entails.eval a c4365 := h 4364 (by decide)
  have h5 : Entails.eval a c4374 := h 4373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9322 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨62, by decide⟩, true), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9322 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9320, some c9321, some c6782, some c3675, some c3793, some c6956, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9322 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9322 : lratChecker f9322 p9322 = .success := by decide +kernel
theorem unsat9322 : Unsatisfiable (PosFin 65) f9322 := by
  apply lratCheckerSound f9322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9322
  · intro a ha; simp [p9322] at ha; subst a; trivial
  · exact checked9322
theorem derived9322 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9322 := by
  apply localUnsat_implies_entails f9322 [c9320, c9321, c6782, c3675, c3793, c6956] c9322 unsat9322 (by rfl) a
  have h0 : Entails.eval a c9320 := derived9320 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c6782 := derived6782 a h
  have h3 : Entails.eval a c3675 := h 3674 (by decide)
  have h4 : Entails.eval a c3793 := h 3792 (by decide)
  have h5 : Entails.eval a c6956 := derived6956 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9323 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9323 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9321, some c3518, some c4348, some c3926, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9323 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9323 : lratChecker f9323 p9323 = .success := by decide +kernel
theorem unsat9323 : Unsatisfiable (PosFin 65) f9323 := by
  apply lratCheckerSound f9323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9323
  · intro a ha; simp [p9323] at ha; subst a; trivial
  · exact checked9323
theorem derived9323 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9323 := by
  apply localUnsat_implies_entails f9323 [c9229, c9321, c3518, c4348, c3926] c9323 unsat9323 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c3518 := h 3517 (by decide)
  have h3 : Entails.eval a c4348 := h 4347 (by decide)
  have h4 : Entails.eval a c3926 := h 3925 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9324 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9324 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c9320, some c9323, some c9321, some c6782, some c9322, some c3785, some c3920, some c4507, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9324 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9324 : lratChecker f9324 p9324 = .success := by decide +kernel
theorem unsat9324 : Unsatisfiable (PosFin 65) f9324 := by
  apply lratCheckerSound f9324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9324
  · intro a ha; simp [p9324] at ha; subst a; trivial
  · exact checked9324
theorem derived9324 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9324 := by
  apply localUnsat_implies_entails f9324 [c9228, c9229, c9320, c9323, c9321, c6782, c9322, c3785, c3920, c4507] c9324 unsat9324 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c9323 := derived9323 a h
  have h4 : Entails.eval a c9321 := derived9321 a h
  have h5 : Entails.eval a c6782 := derived6782 a h
  have h6 : Entails.eval a c9322 := derived9322 a h
  have h7 : Entails.eval a c3785 := h 3784 (by decide)
  have h8 : Entails.eval a c3920 := h 3919 (by decide)
  have h9 : Entails.eval a c4507 := h 4506 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9325 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨40, by decide⟩, false), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9325 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c3920, some c4507, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9325 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9325 : lratChecker f9325 p9325 = .success := by decide +kernel
theorem unsat9325 : Unsatisfiable (PosFin 65) f9325 := by
  apply lratCheckerSound f9325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9325
  · intro a ha; simp [p9325] at ha; subst a; trivial
  · exact checked9325
theorem derived9325 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9325 := by
  apply localUnsat_implies_entails f9325 [c9228, c9229, c3920, c4507] c9325 unsat9325 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c3920 := h 3919 (by decide)
  have h3 : Entails.eval a c4507 := h 4506 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9326 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9326 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9320, some c9321, some c9323, some c9324, some c3519, some c3787, some c5071, some c5099, some c3902, some c9068, some c9325, some c4919, some c3914, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9326 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9326 : lratChecker f9326 p9326 = .success := by decide +kernel
theorem unsat9326 : Unsatisfiable (PosFin 65) f9326 := by
  apply lratCheckerSound f9326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9326
  · intro a ha; simp [p9326] at ha; subst a; trivial
  · exact checked9326
theorem derived9326 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9326 := by
  apply localUnsat_implies_entails f9326 [c9229, c9320, c9321, c9323, c9324, c3519, c3787, c5071, c5099, c3902, c9068, c9325, c4919, c3914] c9326 unsat9326 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9320 := derived9320 a h
  have h2 : Entails.eval a c9321 := derived9321 a h
  have h3 : Entails.eval a c9323 := derived9323 a h
  have h4 : Entails.eval a c9324 := derived9324 a h
  have h5 : Entails.eval a c3519 := h 3518 (by decide)
  have h6 : Entails.eval a c3787 := h 3786 (by decide)
  have h7 : Entails.eval a c5071 := h 5070 (by decide)
  have h8 : Entails.eval a c5099 := h 5098 (by decide)
  have h9 : Entails.eval a c3902 := h 3901 (by decide)
  have h10 : Entails.eval a c9068 := derived9068 a h
  have h11 : Entails.eval a c9325 := derived9325 a h
  have h12 : Entails.eval a c4919 := h 4918 (by decide)
  have h13 : Entails.eval a c3914 := h 3913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9327 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨61, by decide⟩, false), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9327 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c3926, some c6858, some c4268, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9327 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9327 : lratChecker f9327 p9327 = .success := by decide +kernel
theorem unsat9327 : Unsatisfiable (PosFin 65) f9327 := by
  apply lratCheckerSound f9327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9327
  · intro a ha; simp [p9327] at ha; subst a; trivial
  · exact checked9327
theorem derived9327 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9327 := by
  apply localUnsat_implies_entails f9327 [c9229, c9228, c3926, c6858, c4268] c9327 unsat9327 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c3926 := h 3925 (by decide)
  have h3 : Entails.eval a c6858 := derived6858 a h
  have h4 : Entails.eval a c4268 := h 4267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9328 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨62, by decide⟩, false), (⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9328 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c9326, some c9320, some c3787, some c5071, some c5099, some c4767, some c3902, some c9068, some c4146, some c6451, some c9327, some c4504, some c4508, some c7008, some c3665, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9328 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9328 : lratChecker f9328 p9328 = .success := by decide +kernel
theorem unsat9328 : Unsatisfiable (PosFin 65) f9328 := by
  apply lratCheckerSound f9328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9328
  · intro a ha; simp [p9328] at ha; subst a; trivial
  · exact checked9328
theorem derived9328 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9328 := by
  apply localUnsat_implies_entails f9328 [c9228, c9229, c9326, c9320, c3787, c5071, c5099, c4767, c3902, c9068, c4146, c6451, c9327, c4504, c4508, c7008, c3665] c9328 unsat9328 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9326 := derived9326 a h
  have h3 : Entails.eval a c9320 := derived9320 a h
  have h4 : Entails.eval a c3787 := h 3786 (by decide)
  have h5 : Entails.eval a c5071 := h 5070 (by decide)
  have h6 : Entails.eval a c5099 := h 5098 (by decide)
  have h7 : Entails.eval a c4767 := h 4766 (by decide)
  have h8 : Entails.eval a c3902 := h 3901 (by decide)
  have h9 : Entails.eval a c9068 := derived9068 a h
  have h10 : Entails.eval a c4146 := h 4145 (by decide)
  have h11 : Entails.eval a c6451 := derived6451 a h
  have h12 : Entails.eval a c9327 := derived9327 a h
  have h13 : Entails.eval a c4504 := h 4503 (by decide)
  have h14 : Entails.eval a c4508 := h 4507 (by decide)
  have h15 : Entails.eval a c7008 := derived7008 a h
  have h16 : Entails.eval a c3665 := h 3664 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9329 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨51, by decide⟩, true), (⟨40, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9329 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c4508, some c5322, some c4697, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9329 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9329 : lratChecker f9329 p9329 = .success := by decide +kernel
theorem unsat9329 : Unsatisfiable (PosFin 65) f9329 := by
  apply lratCheckerSound f9329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9329
  · intro a ha; simp [p9329] at ha; subst a; trivial
  · exact checked9329
theorem derived9329 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9329 := by
  apply localUnsat_implies_entails f9329 [c9229, c4508, c5322, c4697] c9329 unsat9329 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c4508 := h 4507 (by decide)
  have h2 : Entails.eval a c5322 := h 5321 (by decide)
  have h3 : Entails.eval a c4697 := h 4696 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9330 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨62, by decide⟩, false), (⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9330 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9326, some c9320, some c9328, some c3573, some c4767, some c5011, some c5641, some c5749, some c5099, some c9122, some c9068, some c9329, some c4332, some c4257, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9330 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9330 : lratChecker f9330 p9330 = .success := by decide +kernel
theorem unsat9330 : Unsatisfiable (PosFin 65) f9330 := by
  apply lratCheckerSound f9330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9330
  · intro a ha; simp [p9330] at ha; subst a; trivial
  · exact checked9330
theorem derived9330 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9330 := by
  apply localUnsat_implies_entails f9330 [c9229, c9326, c9320, c9328, c3573, c4767, c5011, c5641, c5749, c5099, c9122, c9068, c9329, c4332, c4257] c9330 unsat9330 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9326 := derived9326 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c9328 := derived9328 a h
  have h4 : Entails.eval a c3573 := h 3572 (by decide)
  have h5 : Entails.eval a c4767 := h 4766 (by decide)
  have h6 : Entails.eval a c5011 := h 5010 (by decide)
  have h7 : Entails.eval a c5641 := h 5640 (by decide)
  have h8 : Entails.eval a c5749 := h 5748 (by decide)
  have h9 : Entails.eval a c5099 := h 5098 (by decide)
  have h10 : Entails.eval a c9122 := derived9122 a h
  have h11 : Entails.eval a c9068 := derived9068 a h
  have h12 : Entails.eval a c9329 := derived9329 a h
  have h13 : Entails.eval a c4332 := h 4331 (by decide)
  have h14 : Entails.eval a c4257 := h 4256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9331 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨48, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9331 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c5875, some c3920, some c4327, some c3493, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9331 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9331 : lratChecker f9331 p9331 = .success := by decide +kernel
theorem unsat9331 : Unsatisfiable (PosFin 65) f9331 := by
  apply lratCheckerSound f9331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9331
  · intro a ha; simp [p9331] at ha; subst a; trivial
  · exact checked9331
theorem derived9331 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9331 := by
  apply localUnsat_implies_entails f9331 [c9229, c9228, c5875, c3920, c4327, c3493] c9331 unsat9331 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c5875 := h 5874 (by decide)
  have h3 : Entails.eval a c3920 := h 3919 (by decide)
  have h4 : Entails.eval a c4327 := h 4326 (by decide)
  have h5 : Entails.eval a c3493 := h 3492 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9332 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨48, by decide⟩, true), (⟨36, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9332 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9331, some c4503, some c4562, some c4824, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9332 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9332 : lratChecker f9332 p9332 = .success := by decide +kernel
theorem unsat9332 : Unsatisfiable (PosFin 65) f9332 := by
  apply lratCheckerSound f9332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9332
  · intro a ha; simp [p9332] at ha; subst a; trivial
  · exact checked9332
theorem derived9332 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9332 := by
  apply localUnsat_implies_entails f9332 [c9228, c9331, c4503, c4562, c4824] c9332 unsat9332 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9331 := derived9331 a h
  have h2 : Entails.eval a c4503 := h 4502 (by decide)
  have h3 : Entails.eval a c4562 := h 4561 (by decide)
  have h4 : Entails.eval a c4824 := h 4823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9333 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨40, by decide⟩, true), (⟨62, by decide⟩, true), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9333 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6938, some c6937, some c6939, some c4812, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p9333 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9333 : lratChecker f9333 p9333 = .success := by decide +kernel
theorem unsat9333 : Unsatisfiable (PosFin 65) f9333 := by
  apply lratCheckerSound f9333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9333
  · intro a ha; simp [p9333] at ha; subst a; trivial
  · exact checked9333
theorem derived9333 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9333 := by
  apply localUnsat_implies_entails f9333 [c6938, c6937, c6939, c4812] c9333 unsat9333 (by rfl) a
  have h0 : Entails.eval a c6938 := derived6938 a h
  have h1 : Entails.eval a c6937 := derived6937 a h
  have h2 : Entails.eval a c6939 := derived6939 a h
  have h3 : Entails.eval a c4812 := h 4811 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9334 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9334 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c4563, some c6900, some c6899, some c4558, some c4551, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9334 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9334 : lratChecker f9334 p9334 = .success := by decide +kernel
theorem unsat9334 : Unsatisfiable (PosFin 65) f9334 := by
  apply lratCheckerSound f9334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9334
  · intro a ha; simp [p9334] at ha; subst a; trivial
  · exact checked9334
theorem derived9334 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9334 := by
  apply localUnsat_implies_entails f9334 [c9228, c4563, c6900, c6899, c4558, c4551] c9334 unsat9334 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c4563 := h 4562 (by decide)
  have h2 : Entails.eval a c6900 := derived6900 a h
  have h3 : Entails.eval a c6899 := derived6899 a h
  have h4 : Entails.eval a c4558 := h 4557 (by decide)
  have h5 : Entails.eval a c4551 := h 4550 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9335 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9335 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9320, some c9326, some c9332, some c9330, some c9334, some c9333, some c4508, some c4871, some c6966, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9335 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9335 : lratChecker f9335 p9335 = .success := by decide +kernel
theorem unsat9335 : Unsatisfiable (PosFin 65) f9335 := by
  apply lratCheckerSound f9335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9335
  · intro a ha; simp [p9335] at ha; subst a; trivial
  · exact checked9335
theorem derived9335 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9335 := by
  apply localUnsat_implies_entails f9335 [c9229, c9320, c9326, c9332, c9330, c9334, c9333, c4508, c4871, c6966] c9335 unsat9335 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9320 := derived9320 a h
  have h2 : Entails.eval a c9326 := derived9326 a h
  have h3 : Entails.eval a c9332 := derived9332 a h
  have h4 : Entails.eval a c9330 := derived9330 a h
  have h5 : Entails.eval a c9334 := derived9334 a h
  have h6 : Entails.eval a c9333 := derived9333 a h
  have h7 : Entails.eval a c4508 := h 4507 (by decide)
  have h8 : Entails.eval a c4871 := h 4870 (by decide)
  have h9 : Entails.eval a c6966 := derived6966 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9336 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9336 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4871, some c6966, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9336 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9336 : lratChecker f9336 p9336 = .success := by decide +kernel
theorem unsat9336 : Unsatisfiable (PosFin 65) f9336 := by
  apply lratCheckerSound f9336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9336
  · intro a ha; simp [p9336] at ha; subst a; trivial
  · exact checked9336
theorem derived9336 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9336 := by
  apply localUnsat_implies_entails f9336 [c4871, c6966] c9336 unsat9336 (by rfl) a
  have h0 : Entails.eval a c4871 := h 4870 (by decide)
  have h1 : Entails.eval a c6966 := derived6966 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9337 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9337 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9335, some c9320, some c9326, some c9332, some c9330, some c9336, some c3926, some c5098, some c3572, some c7035, some c5766, some c7037, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9337 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9337 : lratChecker f9337 p9337 = .success := by decide +kernel
theorem unsat9337 : Unsatisfiable (PosFin 65) f9337 := by
  apply lratCheckerSound f9337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9337
  · intro a ha; simp [p9337] at ha; subst a; trivial
  · exact checked9337
theorem derived9337 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9337 := by
  apply localUnsat_implies_entails f9337 [c9229, c9335, c9320, c9326, c9332, c9330, c9336, c3926, c5098, c3572, c7035, c5766, c7037] c9337 unsat9337 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9335 := derived9335 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c9326 := derived9326 a h
  have h4 : Entails.eval a c9332 := derived9332 a h
  have h5 : Entails.eval a c9330 := derived9330 a h
  have h6 : Entails.eval a c9336 := derived9336 a h
  have h7 : Entails.eval a c3926 := h 3925 (by decide)
  have h8 : Entails.eval a c5098 := h 5097 (by decide)
  have h9 : Entails.eval a c3572 := h 3571 (by decide)
  have h10 : Entails.eval a c7035 := derived7035 a h
  have h11 : Entails.eval a c5766 := h 5765 (by decide)
  have h12 : Entails.eval a c7037 := derived7037 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9338 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, true), (⟨62, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9338 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c3926, some c3543, some c6193, some c6785, some c3540, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9338 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9338 : lratChecker f9338 p9338 = .success := by decide +kernel
theorem unsat9338 : Unsatisfiable (PosFin 65) f9338 := by
  apply lratCheckerSound f9338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9338
  · intro a ha; simp [p9338] at ha; subst a; trivial
  · exact checked9338
theorem derived9338 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9338 := by
  apply localUnsat_implies_entails f9338 [c9229, c9228, c3926, c3543, c6193, c6785, c3540] c9338 unsat9338 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c3926 := h 3925 (by decide)
  have h3 : Entails.eval a c3543 := h 3542 (by decide)
  have h4 : Entails.eval a c6193 := derived6193 a h
  have h5 : Entails.eval a c6785 := derived6785 a h
  have h6 : Entails.eval a c3540 := h 3539 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9339 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9339 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9335, some c9320, some c9326, some c9332, some c9330, some c9337, some c9338, some c3549, some c4992, some c3675, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9339 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9339 : lratChecker f9339 p9339 = .success := by decide +kernel
theorem unsat9339 : Unsatisfiable (PosFin 65) f9339 := by
  apply lratCheckerSound f9339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9339
  · intro a ha; simp [p9339] at ha; subst a; trivial
  · exact checked9339
theorem derived9339 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9339 := by
  apply localUnsat_implies_entails f9339 [c9335, c9320, c9326, c9332, c9330, c9337, c9338, c3549, c4992, c3675] c9339 unsat9339 (by rfl) a
  have h0 : Entails.eval a c9335 := derived9335 a h
  have h1 : Entails.eval a c9320 := derived9320 a h
  have h2 : Entails.eval a c9326 := derived9326 a h
  have h3 : Entails.eval a c9332 := derived9332 a h
  have h4 : Entails.eval a c9330 := derived9330 a h
  have h5 : Entails.eval a c9337 := derived9337 a h
  have h6 : Entails.eval a c9338 := derived9338 a h
  have h7 : Entails.eval a c3549 := h 3548 (by decide)
  have h8 : Entails.eval a c4992 := h 4991 (by decide)
  have h9 : Entails.eval a c3675 := h 3674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9340 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9340 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9326, some c9320, some c9332, some c9330, some c9335, some c9339, some c9333, some c9338, some c3549, some c3793, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9340 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9340 : lratChecker f9340 p9340 = .success := by decide +kernel
theorem unsat9340 : Unsatisfiable (PosFin 65) f9340 := by
  apply lratCheckerSound f9340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9340
  · intro a ha; simp [p9340] at ha; subst a; trivial
  · exact checked9340
theorem derived9340 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9340 := by
  apply localUnsat_implies_entails f9340 [c9326, c9320, c9332, c9330, c9335, c9339, c9333, c9338, c3549, c3793] c9340 unsat9340 (by rfl) a
  have h0 : Entails.eval a c9326 := derived9326 a h
  have h1 : Entails.eval a c9320 := derived9320 a h
  have h2 : Entails.eval a c9332 := derived9332 a h
  have h3 : Entails.eval a c9330 := derived9330 a h
  have h4 : Entails.eval a c9335 := derived9335 a h
  have h5 : Entails.eval a c9339 := derived9339 a h
  have h6 : Entails.eval a c9333 := derived9333 a h
  have h7 : Entails.eval a c9338 := derived9338 a h
  have h8 : Entails.eval a c3549 := h 3548 (by decide)
  have h9 : Entails.eval a c3793 := h 3792 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9341 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9341 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4576, some c4591, some c4592, some c4577, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p9341 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9341 : lratChecker f9341 p9341 = .success := by decide +kernel
theorem unsat9341 : Unsatisfiable (PosFin 65) f9341 := by
  apply lratCheckerSound f9341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9341
  · intro a ha; simp [p9341] at ha; subst a; trivial
  · exact checked9341
theorem derived9341 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9341 := by
  apply localUnsat_implies_entails f9341 [c4576, c4591, c4592, c4577] c9341 unsat9341 (by rfl) a
  have h0 : Entails.eval a c4576 := h 4575 (by decide)
  have h1 : Entails.eval a c4591 := h 4590 (by decide)
  have h2 : Entails.eval a c4592 := h 4591 (by decide)
  have h3 : Entails.eval a c4577 := h 4576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9342 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨62, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9342 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9340, some c9326, some c9320, some c9341, some c9333, some c9336, some c5193, some c5039, some c4508, some c5546, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9342 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9342 : lratChecker f9342 p9342 = .success := by decide +kernel
theorem unsat9342 : Unsatisfiable (PosFin 65) f9342 := by
  apply lratCheckerSound f9342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9342
  · intro a ha; simp [p9342] at ha; subst a; trivial
  · exact checked9342
theorem derived9342 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9342 := by
  apply localUnsat_implies_entails f9342 [c9229, c9340, c9326, c9320, c9341, c9333, c9336, c5193, c5039, c4508, c5546] c9342 unsat9342 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9340 := derived9340 a h
  have h2 : Entails.eval a c9326 := derived9326 a h
  have h3 : Entails.eval a c9320 := derived9320 a h
  have h4 : Entails.eval a c9341 := derived9341 a h
  have h5 : Entails.eval a c9333 := derived9333 a h
  have h6 : Entails.eval a c9336 := derived9336 a h
  have h7 : Entails.eval a c5193 := h 5192 (by decide)
  have h8 : Entails.eval a c5039 := h 5038 (by decide)
  have h9 : Entails.eval a c4508 := h 4507 (by decide)
  have h10 : Entails.eval a c5546 := h 5545 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9343 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨36, by decide⟩, true), (⟨35, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9343 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c4614, some c4585, some c4864, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9343 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9343 : lratChecker f9343 p9343 = .success := by decide +kernel
theorem unsat9343 : Unsatisfiable (PosFin 65) f9343 := by
  apply lratCheckerSound f9343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9343
  · intro a ha; simp [p9343] at ha; subst a; trivial
  · exact checked9343
theorem derived9343 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9343 := by
  apply localUnsat_implies_entails f9343 [c9229, c9228, c4614, c4585, c4864] c9343 unsat9343 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c4614 := h 4613 (by decide)
  have h3 : Entails.eval a c4585 := h 4584 (by decide)
  have h4 : Entails.eval a c4864 := h 4863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9344 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9344 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9320, some c9326, some c9340, some c9343, some c9342, some c5040, some c5194, some c4767, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9344 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9344 : lratChecker f9344 p9344 = .success := by decide +kernel
theorem unsat9344 : Unsatisfiable (PosFin 65) f9344 := by
  apply lratCheckerSound f9344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9344
  · intro a ha; simp [p9344] at ha; subst a; trivial
  · exact checked9344
theorem derived9344 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9344 := by
  apply localUnsat_implies_entails f9344 [c9229, c9320, c9326, c9340, c9343, c9342, c5040, c5194, c4767] c9344 unsat9344 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9320 := derived9320 a h
  have h2 : Entails.eval a c9326 := derived9326 a h
  have h3 : Entails.eval a c9340 := derived9340 a h
  have h4 : Entails.eval a c9343 := derived9343 a h
  have h5 : Entails.eval a c9342 := derived9342 a h
  have h6 : Entails.eval a c5040 := h 5039 (by decide)
  have h7 : Entails.eval a c5194 := h 5193 (by decide)
  have h8 : Entails.eval a c4767 := h 4766 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9345 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨48, by decide⟩, false), (⟨54, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9345 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c5040, some c5194, some c5250, some c5522, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9345 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9345 : lratChecker f9345 p9345 = .success := by decide +kernel
theorem unsat9345 : Unsatisfiable (PosFin 65) f9345 := by
  apply lratCheckerSound f9345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9345
  · intro a ha; simp [p9345] at ha; subst a; trivial
  · exact checked9345
theorem derived9345 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9345 := by
  apply localUnsat_implies_entails f9345 [c9229, c5040, c5194, c5250, c5522] c9345 unsat9345 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c5040 := h 5039 (by decide)
  have h2 : Entails.eval a c5194 := h 5193 (by decide)
  have h3 : Entails.eval a c5250 := h 5249 (by decide)
  have h4 : Entails.eval a c5522 := h 5521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9346 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨39, by decide⟩, true), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9346 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9344, some c9320, some c4468, some c6886, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9346 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9346 : lratChecker f9346 p9346 = .success := by decide +kernel
theorem unsat9346 : Unsatisfiable (PosFin 65) f9346 := by
  apply lratCheckerSound f9346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9346
  · intro a ha; simp [p9346] at ha; subst a; trivial
  · exact checked9346
theorem derived9346 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9346 := by
  apply localUnsat_implies_entails f9346 [c9229, c9344, c9320, c4468, c6886] c9346 unsat9346 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9344 := derived9344 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c4468 := h 4467 (by decide)
  have h4 : Entails.eval a c6886 := derived6886 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9347 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9347 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9320, some c9345, some c5249, some c5246, some c5253, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9347 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9347 : lratChecker f9347 p9347 = .success := by decide +kernel
theorem unsat9347 : Unsatisfiable (PosFin 65) f9347 := by
  apply lratCheckerSound f9347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9347
  · intro a ha; simp [p9347] at ha; subst a; trivial
  · exact checked9347
theorem derived9347 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9347 := by
  apply localUnsat_implies_entails f9347 [c9229, c9320, c9345, c5249, c5246, c5253] c9347 unsat9347 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9320 := derived9320 a h
  have h2 : Entails.eval a c9345 := derived9345 a h
  have h3 : Entails.eval a c5249 := h 5248 (by decide)
  have h4 : Entails.eval a c5246 := h 5245 (by decide)
  have h5 : Entails.eval a c5253 := h 5252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9348 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9348 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9344, some c9320, some c9345, some c9347, some c9346, some c5039, some c6952, some c6881, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9348 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9348 : lratChecker f9348 p9348 = .success := by decide +kernel
theorem unsat9348 : Unsatisfiable (PosFin 65) f9348 := by
  apply lratCheckerSound f9348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9348
  · intro a ha; simp [p9348] at ha; subst a; trivial
  · exact checked9348
theorem derived9348 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9348 := by
  apply localUnsat_implies_entails f9348 [c9229, c9344, c9320, c9345, c9347, c9346, c5039, c6952, c6881] c9348 unsat9348 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9344 := derived9344 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c9345 := derived9345 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c9346 := derived9346 a h
  have h6 : Entails.eval a c5039 := h 5038 (by decide)
  have h7 : Entails.eval a c6952 := derived6952 a h
  have h8 : Entails.eval a c6881 := derived6881 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9349 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨45, by decide⟩, true), (⟨39, by decide⟩, false), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9349 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9344, some c6881, some c6952, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9349 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9349 : lratChecker f9349 p9349 = .success := by decide +kernel
theorem unsat9349 : Unsatisfiable (PosFin 65) f9349 := by
  apply lratCheckerSound f9349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9349
  · intro a ha; simp [p9349] at ha; subst a; trivial
  · exact checked9349
theorem derived9349 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9349 := by
  apply localUnsat_implies_entails f9349 [c9344, c6881, c6952] c9349 unsat9349 (by rfl) a
  have h0 : Entails.eval a c9344 := derived9344 a h
  have h1 : Entails.eval a c6881 := derived6881 a h
  have h2 : Entails.eval a c6952 := derived6952 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9350 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨39, by decide⟩, false), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9350 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9348, some c9344, some c9320, some c9349, some c4637, some c5010, some c4145, some c5640, some c4332, some c4927, some c9080, some c6949, some c6919, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9350 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9350 : lratChecker f9350 p9350 = .success := by decide +kernel
theorem unsat9350 : Unsatisfiable (PosFin 65) f9350 := by
  apply lratCheckerSound f9350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9350
  · intro a ha; simp [p9350] at ha; subst a; trivial
  · exact checked9350
theorem derived9350 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9350 := by
  apply localUnsat_implies_entails f9350 [c9229, c9348, c9344, c9320, c9349, c4637, c5010, c4145, c5640, c4332, c4927, c9080, c6949, c6919] c9350 unsat9350 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9348 := derived9348 a h
  have h2 : Entails.eval a c9344 := derived9344 a h
  have h3 : Entails.eval a c9320 := derived9320 a h
  have h4 : Entails.eval a c9349 := derived9349 a h
  have h5 : Entails.eval a c4637 := h 4636 (by decide)
  have h6 : Entails.eval a c5010 := h 5009 (by decide)
  have h7 : Entails.eval a c4145 := h 4144 (by decide)
  have h8 : Entails.eval a c5640 := h 5639 (by decide)
  have h9 : Entails.eval a c4332 := h 4331 (by decide)
  have h10 : Entails.eval a c4927 := h 4926 (by decide)
  have h11 : Entails.eval a c9080 := derived9080 a h
  have h12 : Entails.eval a c6949 := derived6949 a h
  have h13 : Entails.eval a c6919 := derived6919 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9351 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨45, by decide⟩, false), (⟨39, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9351 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9348, some c9320, some c5098, some c5010, some c5640, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9351 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9351 : lratChecker f9351 p9351 = .success := by decide +kernel
theorem unsat9351 : Unsatisfiable (PosFin 65) f9351 := by
  apply lratCheckerSound f9351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9351
  · intro a ha; simp [p9351] at ha; subst a; trivial
  · exact checked9351
theorem derived9351 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9351 := by
  apply localUnsat_implies_entails f9351 [c9229, c9348, c9320, c5098, c5010, c5640] c9351 unsat9351 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9348 := derived9348 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c5098 := h 5097 (by decide)
  have h4 : Entails.eval a c5010 := h 5009 (by decide)
  have h5 : Entails.eval a c5640 := h 5639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9352 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9352 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9348, some c9320, some c9350, some c9351, some c6971, some c6961, some c5643, some c5638, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9352 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9352 : lratChecker f9352 p9352 = .success := by decide +kernel
theorem unsat9352 : Unsatisfiable (PosFin 65) f9352 := by
  apply lratCheckerSound f9352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9352
  · intro a ha; simp [p9352] at ha; subst a; trivial
  · exact checked9352
theorem derived9352 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9352 := by
  apply localUnsat_implies_entails f9352 [c9229, c9348, c9320, c9350, c9351, c6971, c6961, c5643, c5638] c9352 unsat9352 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9348 := derived9348 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c9350 := derived9350 a h
  have h4 : Entails.eval a c9351 := derived9351 a h
  have h5 : Entails.eval a c6971 := derived6971 a h
  have h6 : Entails.eval a c6961 := derived6961 a h
  have h7 : Entails.eval a c5643 := h 5642 (by decide)
  have h8 : Entails.eval a c5638 := h 5637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9353 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9353 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9352, some c9346, some c9348, some c9320, some c6971, some c6980, some c5643, some c5638, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9353 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9353 : lratChecker f9353 p9353 = .success := by decide +kernel
theorem unsat9353 : Unsatisfiable (PosFin 65) f9353 := by
  apply lratCheckerSound f9353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9353
  · intro a ha; simp [p9353] at ha; subst a; trivial
  · exact checked9353
theorem derived9353 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9353 := by
  apply localUnsat_implies_entails f9353 [c9229, c9352, c9346, c9348, c9320, c6971, c6980, c5643, c5638] c9353 unsat9353 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9352 := derived9352 a h
  have h2 : Entails.eval a c9346 := derived9346 a h
  have h3 : Entails.eval a c9348 := derived9348 a h
  have h4 : Entails.eval a c9320 := derived9320 a h
  have h5 : Entails.eval a c6971 := derived6971 a h
  have h6 : Entails.eval a c6980 := derived6980 a h
  have h7 : Entails.eval a c5643 := h 5642 (by decide)
  have h8 : Entails.eval a c5638 := h 5637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9354 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9354 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9348, some c9320, some c9352, some c9346, some c9353, some c5098, some c5150, some c5640, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9354 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9354 : lratChecker f9354 p9354 = .success := by decide +kernel
theorem unsat9354 : Unsatisfiable (PosFin 65) f9354 := by
  apply lratCheckerSound f9354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9354
  · intro a ha; simp [p9354] at ha; subst a; trivial
  · exact checked9354
theorem derived9354 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9354 := by
  apply localUnsat_implies_entails f9354 [c9229, c9348, c9320, c9352, c9346, c9353, c5098, c5150, c5640] c9354 unsat9354 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9348 := derived9348 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c9352 := derived9352 a h
  have h4 : Entails.eval a c9346 := derived9346 a h
  have h5 : Entails.eval a c9353 := derived9353 a h
  have h6 : Entails.eval a c5098 := h 5097 (by decide)
  have h7 : Entails.eval a c5150 := h 5149 (by decide)
  have h8 : Entails.eval a c5640 := h 5639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9355 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9355 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9354, some c9348, some c9320, some c5099, some c5151, some c5641, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9355 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9355 : lratChecker f9355 p9355 = .success := by decide +kernel
theorem unsat9355 : Unsatisfiable (PosFin 65) f9355 := by
  apply lratCheckerSound f9355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9355
  · intro a ha; simp [p9355] at ha; subst a; trivial
  · exact checked9355
theorem derived9355 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9355 := by
  apply localUnsat_implies_entails f9355 [c9229, c9354, c9348, c9320, c5099, c5151, c5641] c9355 unsat9355 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9354 := derived9354 a h
  have h2 : Entails.eval a c9348 := derived9348 a h
  have h3 : Entails.eval a c9320 := derived9320 a h
  have h4 : Entails.eval a c5099 := h 5098 (by decide)
  have h5 : Entails.eval a c5151 := h 5150 (by decide)
  have h6 : Entails.eval a c5641 := h 5640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9356 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨38, by decide⟩, true), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9356 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9320, some c9354, some c9344, some c9355, some c4638, some c4469, some c4146, some c9348, some c4332, some c4927, some c4198, some c5071, some c3303, some c3138, some c2925, some c2914, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9356 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9356 : lratChecker f9356 p9356 = .success := by decide +kernel
theorem unsat9356 : Unsatisfiable (PosFin 65) f9356 := by
  apply lratCheckerSound f9356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9356
  · intro a ha; simp [p9356] at ha; subst a; trivial
  · exact checked9356
theorem derived9356 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9356 := by
  apply localUnsat_implies_entails f9356 [c9229, c9320, c9354, c9344, c9355, c4638, c4469, c4146, c9348, c4332, c4927, c4198, c5071, c3303, c3138, c2925, c2914] c9356 unsat9356 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9320 := derived9320 a h
  have h2 : Entails.eval a c9354 := derived9354 a h
  have h3 : Entails.eval a c9344 := derived9344 a h
  have h4 : Entails.eval a c9355 := derived9355 a h
  have h5 : Entails.eval a c4638 := h 4637 (by decide)
  have h6 : Entails.eval a c4469 := h 4468 (by decide)
  have h7 : Entails.eval a c4146 := h 4145 (by decide)
  have h8 : Entails.eval a c9348 := derived9348 a h
  have h9 : Entails.eval a c4332 := h 4331 (by decide)
  have h10 : Entails.eval a c4927 := h 4926 (by decide)
  have h11 : Entails.eval a c4198 := h 4197 (by decide)
  have h12 : Entails.eval a c5071 := h 5070 (by decide)
  have h13 : Entails.eval a c3303 := h 3302 (by decide)
  have h14 : Entails.eval a c3138 := h 3137 (by decide)
  have h15 : Entails.eval a c2925 := h 2924 (by decide)
  have h16 : Entails.eval a c2914 := h 2913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9357 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9357 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3308, some c3296, some c3290, some c3389, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9357 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9357 : lratChecker f9357 p9357 = .success := by decide +kernel
theorem unsat9357 : Unsatisfiable (PosFin 65) f9357 := by
  apply lratCheckerSound f9357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9357
  · intro a ha; simp [p9357] at ha; subst a; trivial
  · exact checked9357
theorem derived9357 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9357 := by
  apply localUnsat_implies_entails f9357 [c3308, c3296, c3290, c3389] c9357 unsat9357 (by rfl) a
  have h0 : Entails.eval a c3308 := h 3307 (by decide)
  have h1 : Entails.eval a c3296 := h 3295 (by decide)
  have h2 : Entails.eval a c3290 := h 3289 (by decide)
  have h3 : Entails.eval a c3389 := h 3388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9358 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨38, by decide⟩, true), (⟨55, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9358 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c9355, some c9354, some c9348, some c9320, some c9344, some c4469, some c4638, some c4146, some c4198, some c5071, some c9068, some c5011, some c5749, some c5891, some c9266, some c4332, some c4927, some c4864, some c3856, some c9357, some c9356, some c3417, some c3413, some c2894, some c3424, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9358 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked9358 : lratChecker f9358 p9358 = .success := by decide +kernel
theorem unsat9358 : Unsatisfiable (PosFin 65) f9358 := by
  apply lratCheckerSound f9358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9358
  · intro a ha; simp [p9358] at ha; subst a; trivial
  · exact checked9358
theorem derived9358 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9358 := by
  apply localUnsat_implies_entails f9358 [c9229, c9228, c9355, c9354, c9348, c9320, c9344, c4469, c4638, c4146, c4198, c5071, c9068, c5011, c5749, c5891, c9266, c4332, c4927, c4864, c3856, c9357, c9356, c3417, c3413, c2894, c3424] c9358 unsat9358 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9355 := derived9355 a h
  have h3 : Entails.eval a c9354 := derived9354 a h
  have h4 : Entails.eval a c9348 := derived9348 a h
  have h5 : Entails.eval a c9320 := derived9320 a h
  have h6 : Entails.eval a c9344 := derived9344 a h
  have h7 : Entails.eval a c4469 := h 4468 (by decide)
  have h8 : Entails.eval a c4638 := h 4637 (by decide)
  have h9 : Entails.eval a c4146 := h 4145 (by decide)
  have h10 : Entails.eval a c4198 := h 4197 (by decide)
  have h11 : Entails.eval a c5071 := h 5070 (by decide)
  have h12 : Entails.eval a c9068 := derived9068 a h
  have h13 : Entails.eval a c5011 := h 5010 (by decide)
  have h14 : Entails.eval a c5749 := h 5748 (by decide)
  have h15 : Entails.eval a c5891 := derived5891 a h
  have h16 : Entails.eval a c9266 := derived9266 a h
  have h17 : Entails.eval a c4332 := h 4331 (by decide)
  have h18 : Entails.eval a c4927 := h 4926 (by decide)
  have h19 : Entails.eval a c4864 := h 4863 (by decide)
  have h20 : Entails.eval a c3856 := h 3855 (by decide)
  have h21 : Entails.eval a c9357 := derived9357 a h
  have h22 : Entails.eval a c9356 := derived9356 a h
  have h23 : Entails.eval a c3417 := h 3416 (by decide)
  have h24 : Entails.eval a c3413 := h 3412 (by decide)
  have h25 : Entails.eval a c2894 := h 2893 (by decide)
  have h26 : Entails.eval a c3424 := h 3423 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9359 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨38, by decide⟩, true), (⟨55, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9359 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c9358, some c9354, some c9348, some c9320, some c9344, some c9355, some c4469, some c4638, some c4146, some c4198, some c4332, some c9080, some c6821, some c5071, some c9068, some c5011, some c5749, some c5891, some c9266, some c4927, some c4864, some c3856, some c2894, some c2770, some c3373, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9359 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked9359 : lratChecker f9359 p9359 = .success := by decide +kernel
theorem unsat9359 : Unsatisfiable (PosFin 65) f9359 := by
  apply lratCheckerSound f9359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9359
  · intro a ha; simp [p9359] at ha; subst a; trivial
  · exact checked9359
theorem derived9359 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9359 := by
  apply localUnsat_implies_entails f9359 [c9228, c9229, c9358, c9354, c9348, c9320, c9344, c9355, c4469, c4638, c4146, c4198, c4332, c9080, c6821, c5071, c9068, c5011, c5749, c5891, c9266, c4927, c4864, c3856, c2894, c2770, c3373] c9359 unsat9359 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9358 := derived9358 a h
  have h3 : Entails.eval a c9354 := derived9354 a h
  have h4 : Entails.eval a c9348 := derived9348 a h
  have h5 : Entails.eval a c9320 := derived9320 a h
  have h6 : Entails.eval a c9344 := derived9344 a h
  have h7 : Entails.eval a c9355 := derived9355 a h
  have h8 : Entails.eval a c4469 := h 4468 (by decide)
  have h9 : Entails.eval a c4638 := h 4637 (by decide)
  have h10 : Entails.eval a c4146 := h 4145 (by decide)
  have h11 : Entails.eval a c4198 := h 4197 (by decide)
  have h12 : Entails.eval a c4332 := h 4331 (by decide)
  have h13 : Entails.eval a c9080 := derived9080 a h
  have h14 : Entails.eval a c6821 := derived6821 a h
  have h15 : Entails.eval a c5071 := h 5070 (by decide)
  have h16 : Entails.eval a c9068 := derived9068 a h
  have h17 : Entails.eval a c5011 := h 5010 (by decide)
  have h18 : Entails.eval a c5749 := h 5748 (by decide)
  have h19 : Entails.eval a c5891 := derived5891 a h
  have h20 : Entails.eval a c9266 := derived9266 a h
  have h21 : Entails.eval a c4927 := h 4926 (by decide)
  have h22 : Entails.eval a c4864 := h 4863 (by decide)
  have h23 : Entails.eval a c3856 := h 3855 (by decide)
  have h24 : Entails.eval a c2894 := h 2893 (by decide)
  have h25 : Entails.eval a c2770 := h 2769 (by decide)
  have h26 : Entails.eval a c3373 := h 3372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9360 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨55, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9360 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c9230, some c9355, some c9354, some c9348, some c9320, some c9344, some c4469, some c4638, some c4146, some c4198, some c5071, some c9068, some c5011, some c5749, some c5891, some c9266, some c4332, some c4927, some c4864, some c3856, some c9080, some c6821, some c9358, some c9359, some c9356, some c2743, some c2868, some c2, some c3214, some c3376, some c3371, some c485, some c98, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9360 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked9360 : lratChecker f9360 p9360 = .success := by decide +kernel
theorem unsat9360 : Unsatisfiable (PosFin 65) f9360 := by
  apply lratCheckerSound f9360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9360
  · intro a ha; simp [p9360] at ha; subst a; trivial
  · exact checked9360
theorem derived9360 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9360 := by
  apply localUnsat_implies_entails f9360 [c9228, c9229, c9230, c9355, c9354, c9348, c9320, c9344, c4469, c4638, c4146, c4198, c5071, c9068, c5011, c5749, c5891, c9266, c4332, c4927, c4864, c3856, c9080, c6821, c9358, c9359, c9356, c2743, c2868, c2, c3214, c3376, c3371, c485, c98] c9360 unsat9360 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9230 := derived9230 a h
  have h3 : Entails.eval a c9355 := derived9355 a h
  have h4 : Entails.eval a c9354 := derived9354 a h
  have h5 : Entails.eval a c9348 := derived9348 a h
  have h6 : Entails.eval a c9320 := derived9320 a h
  have h7 : Entails.eval a c9344 := derived9344 a h
  have h8 : Entails.eval a c4469 := h 4468 (by decide)
  have h9 : Entails.eval a c4638 := h 4637 (by decide)
  have h10 : Entails.eval a c4146 := h 4145 (by decide)
  have h11 : Entails.eval a c4198 := h 4197 (by decide)
  have h12 : Entails.eval a c5071 := h 5070 (by decide)
  have h13 : Entails.eval a c9068 := derived9068 a h
  have h14 : Entails.eval a c5011 := h 5010 (by decide)
  have h15 : Entails.eval a c5749 := h 5748 (by decide)
  have h16 : Entails.eval a c5891 := derived5891 a h
  have h17 : Entails.eval a c9266 := derived9266 a h
  have h18 : Entails.eval a c4332 := h 4331 (by decide)
  have h19 : Entails.eval a c4927 := h 4926 (by decide)
  have h20 : Entails.eval a c4864 := h 4863 (by decide)
  have h21 : Entails.eval a c3856 := h 3855 (by decide)
  have h22 : Entails.eval a c9080 := derived9080 a h
  have h23 : Entails.eval a c6821 := derived6821 a h
  have h24 : Entails.eval a c9358 := derived9358 a h
  have h25 : Entails.eval a c9359 := derived9359 a h
  have h26 : Entails.eval a c9356 := derived9356 a h
  have h27 : Entails.eval a c2743 := h 2742 (by decide)
  have h28 : Entails.eval a c2868 := h 2867 (by decide)
  have h29 : Entails.eval a c2 := h 1 (by decide)
  have h30 : Entails.eval a c3214 := h 3213 (by decide)
  have h31 : Entails.eval a c3376 := h 3375 (by decide)
  have h32 : Entails.eval a c3371 := h 3370 (by decide)
  have h33 : Entails.eval a c485 := h 484 (by decide)
  have h34 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9361 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨55, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9361 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c9230, some c9354, some c9348, some c9320, some c9344, some c9355, some c4469, some c4638, some c4146, some c4198, some c4332, some c9080, some c5071, some c4927, some c4864, some c9360, some c6989, some c9068, some c5011, some c5749, some c5891, some c9266, some c9357, some c2743, some c2869, some c3, some c3216, some c3376, some c3371, some c486, some c98, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9361 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked9361 : lratChecker f9361 p9361 = .success := by decide +kernel
theorem unsat9361 : Unsatisfiable (PosFin 65) f9361 := by
  apply lratCheckerSound f9361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9361
  · intro a ha; simp [p9361] at ha; subst a; trivial
  · exact checked9361
theorem derived9361 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9361 := by
  apply localUnsat_implies_entails f9361 [c9228, c9229, c9230, c9354, c9348, c9320, c9344, c9355, c4469, c4638, c4146, c4198, c4332, c9080, c5071, c4927, c4864, c9360, c6989, c9068, c5011, c5749, c5891, c9266, c9357, c2743, c2869, c3, c3216, c3376, c3371, c486, c98] c9361 unsat9361 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9230 := derived9230 a h
  have h3 : Entails.eval a c9354 := derived9354 a h
  have h4 : Entails.eval a c9348 := derived9348 a h
  have h5 : Entails.eval a c9320 := derived9320 a h
  have h6 : Entails.eval a c9344 := derived9344 a h
  have h7 : Entails.eval a c9355 := derived9355 a h
  have h8 : Entails.eval a c4469 := h 4468 (by decide)
  have h9 : Entails.eval a c4638 := h 4637 (by decide)
  have h10 : Entails.eval a c4146 := h 4145 (by decide)
  have h11 : Entails.eval a c4198 := h 4197 (by decide)
  have h12 : Entails.eval a c4332 := h 4331 (by decide)
  have h13 : Entails.eval a c9080 := derived9080 a h
  have h14 : Entails.eval a c5071 := h 5070 (by decide)
  have h15 : Entails.eval a c4927 := h 4926 (by decide)
  have h16 : Entails.eval a c4864 := h 4863 (by decide)
  have h17 : Entails.eval a c9360 := derived9360 a h
  have h18 : Entails.eval a c6989 := derived6989 a h
  have h19 : Entails.eval a c9068 := derived9068 a h
  have h20 : Entails.eval a c5011 := h 5010 (by decide)
  have h21 : Entails.eval a c5749 := h 5748 (by decide)
  have h22 : Entails.eval a c5891 := derived5891 a h
  have h23 : Entails.eval a c9266 := derived9266 a h
  have h24 : Entails.eval a c9357 := derived9357 a h
  have h25 : Entails.eval a c2743 := h 2742 (by decide)
  have h26 : Entails.eval a c2869 := h 2868 (by decide)
  have h27 : Entails.eval a c3 := h 2 (by decide)
  have h28 : Entails.eval a c3216 := h 3215 (by decide)
  have h29 : Entails.eval a c3376 := h 3375 (by decide)
  have h30 : Entails.eval a c3371 := h 3370 (by decide)
  have h31 : Entails.eval a c486 := h 485 (by decide)
  have h32 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9362 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9362 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c9361, some c9354, some c9348, some c9320, some c9344, some c9355, some c4469, some c4638, some c4146, some c4198, some c4332, some c9080, some c5071, some c4927, some c4864, some c9360, some c6989, some c5011, some c5749, some c2888, some c2821, some c3300, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9362 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked9362 : lratChecker f9362 p9362 = .success := by decide +kernel
theorem unsat9362 : Unsatisfiable (PosFin 65) f9362 := by
  apply lratCheckerSound f9362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9362
  · intro a ha; simp [p9362] at ha; subst a; trivial
  · exact checked9362
theorem derived9362 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9362 := by
  apply localUnsat_implies_entails f9362 [c9228, c9229, c9361, c9354, c9348, c9320, c9344, c9355, c4469, c4638, c4146, c4198, c4332, c9080, c5071, c4927, c4864, c9360, c6989, c5011, c5749, c2888, c2821, c3300] c9362 unsat9362 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9361 := derived9361 a h
  have h3 : Entails.eval a c9354 := derived9354 a h
  have h4 : Entails.eval a c9348 := derived9348 a h
  have h5 : Entails.eval a c9320 := derived9320 a h
  have h6 : Entails.eval a c9344 := derived9344 a h
  have h7 : Entails.eval a c9355 := derived9355 a h
  have h8 : Entails.eval a c4469 := h 4468 (by decide)
  have h9 : Entails.eval a c4638 := h 4637 (by decide)
  have h10 : Entails.eval a c4146 := h 4145 (by decide)
  have h11 : Entails.eval a c4198 := h 4197 (by decide)
  have h12 : Entails.eval a c4332 := h 4331 (by decide)
  have h13 : Entails.eval a c9080 := derived9080 a h
  have h14 : Entails.eval a c5071 := h 5070 (by decide)
  have h15 : Entails.eval a c4927 := h 4926 (by decide)
  have h16 : Entails.eval a c4864 := h 4863 (by decide)
  have h17 : Entails.eval a c9360 := derived9360 a h
  have h18 : Entails.eval a c6989 := derived6989 a h
  have h19 : Entails.eval a c5011 := h 5010 (by decide)
  have h20 : Entails.eval a c5749 := h 5748 (by decide)
  have h21 : Entails.eval a c2888 := h 2887 (by decide)
  have h22 : Entails.eval a c2821 := h 2820 (by decide)
  have h23 : Entails.eval a c3300 := h 3299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9363 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9363 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9355, some c9354, some c9348, some c9320, some c9344, some c4469, some c4638, some c4146, some c4198, some c5071, some c9068, some c5011, some c5749, some c5891, some c9266, some c9360, some c9361, some c9362, some c2922, some c3309, some c2906, some c3055, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9363 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9363 : lratChecker f9363 p9363 = .success := by decide +kernel
theorem unsat9363 : Unsatisfiable (PosFin 65) f9363 := by
  apply lratCheckerSound f9363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9363
  · intro a ha; simp [p9363] at ha; subst a; trivial
  · exact checked9363
theorem derived9363 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9363 := by
  apply localUnsat_implies_entails f9363 [c9229, c9355, c9354, c9348, c9320, c9344, c4469, c4638, c4146, c4198, c5071, c9068, c5011, c5749, c5891, c9266, c9360, c9361, c9362, c2922, c3309, c2906, c3055] c9363 unsat9363 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9355 := derived9355 a h
  have h2 : Entails.eval a c9354 := derived9354 a h
  have h3 : Entails.eval a c9348 := derived9348 a h
  have h4 : Entails.eval a c9320 := derived9320 a h
  have h5 : Entails.eval a c9344 := derived9344 a h
  have h6 : Entails.eval a c4469 := h 4468 (by decide)
  have h7 : Entails.eval a c4638 := h 4637 (by decide)
  have h8 : Entails.eval a c4146 := h 4145 (by decide)
  have h9 : Entails.eval a c4198 := h 4197 (by decide)
  have h10 : Entails.eval a c5071 := h 5070 (by decide)
  have h11 : Entails.eval a c9068 := derived9068 a h
  have h12 : Entails.eval a c5011 := h 5010 (by decide)
  have h13 : Entails.eval a c5749 := h 5748 (by decide)
  have h14 : Entails.eval a c5891 := derived5891 a h
  have h15 : Entails.eval a c9266 := derived9266 a h
  have h16 : Entails.eval a c9360 := derived9360 a h
  have h17 : Entails.eval a c9361 := derived9361 a h
  have h18 : Entails.eval a c9362 := derived9362 a h
  have h19 : Entails.eval a c2922 := h 2921 (by decide)
  have h20 : Entails.eval a c3309 := h 3308 (by decide)
  have h21 : Entails.eval a c2906 := h 2905 (by decide)
  have h22 : Entails.eval a c3055 := h 3054 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9364 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9364 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c9363, some c9354, some c9348, some c9320, some c9344, some c9355, some c4469, some c4638, some c4146, some c4198, some c4332, some c9080, some c5011, some c5749, some c5425, some c5438, some c5291, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9364 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9364 : lratChecker f9364 p9364 = .success := by decide +kernel
theorem unsat9364 : Unsatisfiable (PosFin 65) f9364 := by
  apply lratCheckerSound f9364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9364
  · intro a ha; simp [p9364] at ha; subst a; trivial
  · exact checked9364
theorem derived9364 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9364 := by
  apply localUnsat_implies_entails f9364 [c9229, c9228, c9363, c9354, c9348, c9320, c9344, c9355, c4469, c4638, c4146, c4198, c4332, c9080, c5011, c5749, c5425, c5438, c5291] c9364 unsat9364 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9363 := derived9363 a h
  have h3 : Entails.eval a c9354 := derived9354 a h
  have h4 : Entails.eval a c9348 := derived9348 a h
  have h5 : Entails.eval a c9320 := derived9320 a h
  have h6 : Entails.eval a c9344 := derived9344 a h
  have h7 : Entails.eval a c9355 := derived9355 a h
  have h8 : Entails.eval a c4469 := h 4468 (by decide)
  have h9 : Entails.eval a c4638 := h 4637 (by decide)
  have h10 : Entails.eval a c4146 := h 4145 (by decide)
  have h11 : Entails.eval a c4198 := h 4197 (by decide)
  have h12 : Entails.eval a c4332 := h 4331 (by decide)
  have h13 : Entails.eval a c9080 := derived9080 a h
  have h14 : Entails.eval a c5011 := h 5010 (by decide)
  have h15 : Entails.eval a c5749 := h 5748 (by decide)
  have h16 : Entails.eval a c5425 := h 5424 (by decide)
  have h17 : Entails.eval a c5438 := h 5437 (by decide)
  have h18 : Entails.eval a c5291 := h 5290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9365 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9365 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9355, some c9354, some c9348, some c9320, some c9344, some c4469, some c4638, some c4146, some c4198, some c5071, some c9068, some c5011, some c4332, some c9080, some c9363, some c9364, some c9303, some c5408, some c5352, some c3967, some c5350, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9365 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9365 : lratChecker f9365 p9365 = .success := by decide +kernel
theorem unsat9365 : Unsatisfiable (PosFin 65) f9365 := by
  apply lratCheckerSound f9365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9365
  · intro a ha; simp [p9365] at ha; subst a; trivial
  · exact checked9365
theorem derived9365 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9365 := by
  apply localUnsat_implies_entails f9365 [c9229, c9355, c9354, c9348, c9320, c9344, c4469, c4638, c4146, c4198, c5071, c9068, c5011, c4332, c9080, c9363, c9364, c9303, c5408, c5352, c3967, c5350] c9365 unsat9365 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9355 := derived9355 a h
  have h2 : Entails.eval a c9354 := derived9354 a h
  have h3 : Entails.eval a c9348 := derived9348 a h
  have h4 : Entails.eval a c9320 := derived9320 a h
  have h5 : Entails.eval a c9344 := derived9344 a h
  have h6 : Entails.eval a c4469 := h 4468 (by decide)
  have h7 : Entails.eval a c4638 := h 4637 (by decide)
  have h8 : Entails.eval a c4146 := h 4145 (by decide)
  have h9 : Entails.eval a c4198 := h 4197 (by decide)
  have h10 : Entails.eval a c5071 := h 5070 (by decide)
  have h11 : Entails.eval a c9068 := derived9068 a h
  have h12 : Entails.eval a c5011 := h 5010 (by decide)
  have h13 : Entails.eval a c4332 := h 4331 (by decide)
  have h14 : Entails.eval a c9080 := derived9080 a h
  have h15 : Entails.eval a c9363 := derived9363 a h
  have h16 : Entails.eval a c9364 := derived9364 a h
  have h17 : Entails.eval a c9303 := derived9303 a h
  have h18 : Entails.eval a c5408 := h 5407 (by decide)
  have h19 : Entails.eval a c5352 := h 5351 (by decide)
  have h20 : Entails.eval a c3967 := h 3966 (by decide)
  have h21 : Entails.eval a c5350 := h 5349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9366 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9366 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9365, some c9355, some c9354, some c9348, some c9320, some c9344, some c4469, some c4638, some c4146, some c4198, some c5071, some c9068, some c3964, some c4074, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9366 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9366 : lratChecker f9366 p9366 = .success := by decide +kernel
theorem unsat9366 : Unsatisfiable (PosFin 65) f9366 := by
  apply lratCheckerSound f9366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9366
  · intro a ha; simp [p9366] at ha; subst a; trivial
  · exact checked9366
theorem derived9366 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9366 := by
  apply localUnsat_implies_entails f9366 [c9229, c9365, c9355, c9354, c9348, c9320, c9344, c4469, c4638, c4146, c4198, c5071, c9068, c3964, c4074] c9366 unsat9366 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9365 := derived9365 a h
  have h2 : Entails.eval a c9355 := derived9355 a h
  have h3 : Entails.eval a c9354 := derived9354 a h
  have h4 : Entails.eval a c9348 := derived9348 a h
  have h5 : Entails.eval a c9320 := derived9320 a h
  have h6 : Entails.eval a c9344 := derived9344 a h
  have h7 : Entails.eval a c4469 := h 4468 (by decide)
  have h8 : Entails.eval a c4638 := h 4637 (by decide)
  have h9 : Entails.eval a c4146 := h 4145 (by decide)
  have h10 : Entails.eval a c4198 := h 4197 (by decide)
  have h11 : Entails.eval a c5071 := h 5070 (by decide)
  have h12 : Entails.eval a c9068 := derived9068 a h
  have h13 : Entails.eval a c3964 := h 3963 (by decide)
  have h14 : Entails.eval a c4074 := h 4073 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9367 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9367 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9320, some c9344, some c9348, some c9354, some c9355, some c4638, some c4469, some c4146, some c5011, some c4198, some c5749, some c9365, some c9366, some c5436, some c6955, some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9367 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9367 : lratChecker f9367 p9367 = .success := by decide +kernel
theorem unsat9367 : Unsatisfiable (PosFin 65) f9367 := by
  apply lratCheckerSound f9367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9367
  · intro a ha; simp [p9367] at ha; subst a; trivial
  · exact checked9367
theorem derived9367 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9367 := by
  apply localUnsat_implies_entails f9367 [c9229, c9320, c9344, c9348, c9354, c9355, c4638, c4469, c4146, c5011, c4198, c5749, c9365, c9366, c5436, c6955] c9367 unsat9367 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9320 := derived9320 a h
  have h2 : Entails.eval a c9344 := derived9344 a h
  have h3 : Entails.eval a c9348 := derived9348 a h
  have h4 : Entails.eval a c9354 := derived9354 a h
  have h5 : Entails.eval a c9355 := derived9355 a h
  have h6 : Entails.eval a c4638 := h 4637 (by decide)
  have h7 : Entails.eval a c4469 := h 4468 (by decide)
  have h8 : Entails.eval a c4146 := h 4145 (by decide)
  have h9 : Entails.eval a c5011 := h 5010 (by decide)
  have h10 : Entails.eval a c4198 := h 4197 (by decide)
  have h11 : Entails.eval a c5749 := h 5748 (by decide)
  have h12 : Entails.eval a c9365 := derived9365 a h
  have h13 : Entails.eval a c9366 := derived9366 a h
  have h14 : Entails.eval a c5436 := h 5435 (by decide)
  have h15 : Entails.eval a c6955 := derived6955 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9368 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨34, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9368 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c6819, some c6839, some c6834, some c6902, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9368 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9368 : lratChecker f9368 p9368 = .success := by decide +kernel
theorem unsat9368 : Unsatisfiable (PosFin 65) f9368 := by
  apply lratCheckerSound f9368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9368
  · intro a ha; simp [p9368] at ha; subst a; trivial
  · exact checked9368
theorem derived9368 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9368 := by
  apply localUnsat_implies_entails f9368 [c9367, c6819, c6839, c6834, c6902] c9368 unsat9368 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c6819 := derived6819 a h
  have h2 : Entails.eval a c6839 := derived6839 a h
  have h3 : Entails.eval a c6834 := derived6834 a h
  have h4 : Entails.eval a c6902 := derived6902 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9369 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9369 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c4564, some c5377, some c5385, some c4566, some c9334, some c5372, some c4552, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9369 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9369 : lratChecker f9369 p9369 = .success := by decide +kernel
theorem unsat9369 : Unsatisfiable (PosFin 65) f9369 := by
  apply lratCheckerSound f9369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9369
  · intro a ha; simp [p9369] at ha; subst a; trivial
  · exact checked9369
theorem derived9369 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9369 := by
  apply localUnsat_implies_entails f9369 [c9228, c4564, c5377, c5385, c4566, c9334, c5372, c4552] c9369 unsat9369 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c4564 := h 4563 (by decide)
  have h2 : Entails.eval a c5377 := h 5376 (by decide)
  have h3 : Entails.eval a c5385 := h 5384 (by decide)
  have h4 : Entails.eval a c4566 := h 4565 (by decide)
  have h5 : Entails.eval a c9334 := derived9334 a h
  have h6 : Entails.eval a c5372 := h 5371 (by decide)
  have h7 : Entails.eval a c4552 := h 4551 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9370 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9370 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c4341, some c4510, some c4825, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9370 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9370 : lratChecker f9370 p9370 = .success := by decide +kernel
theorem unsat9370 : Unsatisfiable (PosFin 65) f9370 := by
  apply lratCheckerSound f9370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9370
  · intro a ha; simp [p9370] at ha; subst a; trivial
  · exact checked9370
theorem derived9370 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9370 := by
  apply localUnsat_implies_entails f9370 [c9229, c9228, c4341, c4510, c4825] c9370 unsat9370 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c4341 := h 4340 (by decide)
  have h3 : Entails.eval a c4510 := h 4509 (by decide)
  have h4 : Entails.eval a c4825 := h 4824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9371 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9371 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9368, some c9369, some c6835, some c9370, some c4020, some c4025, some c4018, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9371 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9371 : lratChecker f9371 p9371 = .success := by decide +kernel
theorem unsat9371 : Unsatisfiable (PosFin 65) f9371 := by
  apply lratCheckerSound f9371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9371
  · intro a ha; simp [p9371] at ha; subst a; trivial
  · exact checked9371
theorem derived9371 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9371 := by
  apply localUnsat_implies_entails f9371 [c9367, c9368, c9369, c6835, c9370, c4020, c4025, c4018] c9371 unsat9371 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9368 := derived9368 a h
  have h2 : Entails.eval a c9369 := derived9369 a h
  have h3 : Entails.eval a c6835 := derived6835 a h
  have h4 : Entails.eval a c9370 := derived9370 a h
  have h5 : Entails.eval a c4020 := h 4019 (by decide)
  have h6 : Entails.eval a c4025 := h 4024 (by decide)
  have h7 : Entails.eval a c4018 := h 4017 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9372 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9372 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9367, some c9228, some c9368, some c9371, some c4043, some c6837, some c4060, some c6836, some c4041, some c4328, some c4265, some c4611, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9372 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9372 : lratChecker f9372 p9372 = .success := by decide +kernel
theorem unsat9372 : Unsatisfiable (PosFin 65) f9372 := by
  apply lratCheckerSound f9372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9372
  · intro a ha; simp [p9372] at ha; subst a; trivial
  · exact checked9372
theorem derived9372 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9372 := by
  apply localUnsat_implies_entails f9372 [c9229, c9367, c9228, c9368, c9371, c4043, c6837, c4060, c6836, c4041, c4328, c4265, c4611] c9372 unsat9372 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c9228 := derived9228 a h
  have h3 : Entails.eval a c9368 := derived9368 a h
  have h4 : Entails.eval a c9371 := derived9371 a h
  have h5 : Entails.eval a c4043 := h 4042 (by decide)
  have h6 : Entails.eval a c6837 := derived6837 a h
  have h7 : Entails.eval a c4060 := h 4059 (by decide)
  have h8 : Entails.eval a c6836 := derived6836 a h
  have h9 : Entails.eval a c4041 := h 4040 (by decide)
  have h10 : Entails.eval a c4328 := h 4327 (by decide)
  have h11 : Entails.eval a c4265 := h 4264 (by decide)
  have h12 : Entails.eval a c4611 := h 4610 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9373 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9373 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9367, some c9368, some c9372, some c6820, some c3946, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9373 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9373 : lratChecker f9373 p9373 = .success := by decide +kernel
theorem unsat9373 : Unsatisfiable (PosFin 65) f9373 := by
  apply lratCheckerSound f9373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9373
  · intro a ha; simp [p9373] at ha; subst a; trivial
  · exact checked9373
theorem derived9373 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9373 := by
  apply localUnsat_implies_entails f9373 [c9229, c9367, c9368, c9372, c6820, c3946] c9373 unsat9373 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c9368 := derived9368 a h
  have h3 : Entails.eval a c9372 := derived9372 a h
  have h4 : Entails.eval a c6820 := derived6820 a h
  have h5 : Entails.eval a c3946 := h 3945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9374 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨35, by decide⟩, true), (⟨57, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9374 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9229, some c4395, some c4412, some c4316, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p9374 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9374 : lratChecker f9374 p9374 = .success := by decide +kernel
theorem unsat9374 : Unsatisfiable (PosFin 65) f9374 := by
  apply lratCheckerSound f9374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9374
  · intro a ha; simp [p9374] at ha; subst a; trivial
  · exact checked9374
theorem derived9374 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9374 := by
  apply localUnsat_implies_entails f9374 [c9367, c9229, c4395, c4412, c4316] c9374 unsat9374 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c4395 := h 4394 (by decide)
  have h3 : Entails.eval a c4412 := h 4411 (by decide)
  have h4 : Entails.eval a c4316 := h 4315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9375 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9375 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9267, some c6870, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p9375 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9375 : lratChecker f9375 p9375 = .success := by decide +kernel
theorem unsat9375 : Unsatisfiable (PosFin 65) f9375 := by
  apply lratCheckerSound f9375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9375
  · intro a ha; simp [p9375] at ha; subst a; trivial
  · exact checked9375
theorem derived9375 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9375 := by
  apply localUnsat_implies_entails f9375 [c9367, c9267, c6870] c9375 unsat9375 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9267 := derived9267 a h
  have h2 : Entails.eval a c6870 := derived6870 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9376 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨57, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9376 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9374, some c6878, some c6831, some c6847, some c6914, some c6886, some c6931, some c6852, some c9235, some c9375, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9376 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9376 : lratChecker f9376 p9376 = .success := by decide +kernel
theorem unsat9376 : Unsatisfiable (PosFin 65) f9376 := by
  apply lratCheckerSound f9376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9376
  · intro a ha; simp [p9376] at ha; subst a; trivial
  · exact checked9376
theorem derived9376 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9376 := by
  apply localUnsat_implies_entails f9376 [c9367, c9374, c6878, c6831, c6847, c6914, c6886, c6931, c6852, c9235, c9375] c9376 unsat9376 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9374 := derived9374 a h
  have h2 : Entails.eval a c6878 := derived6878 a h
  have h3 : Entails.eval a c6831 := derived6831 a h
  have h4 : Entails.eval a c6847 := derived6847 a h
  have h5 : Entails.eval a c6914 := derived6914 a h
  have h6 : Entails.eval a c6886 := derived6886 a h
  have h7 : Entails.eval a c6931 := derived6931 a h
  have h8 : Entails.eval a c6852 := derived6852 a h
  have h9 : Entails.eval a c9235 := derived9235 a h
  have h10 : Entails.eval a c9375 := derived9375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9377 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨57, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9377 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9228, some c9373, some c9376, some c9369, some c6990, some c7000, some c6987, some c6986, some c5564, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9377 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9377 : lratChecker f9377 p9377 = .success := by decide +kernel
theorem unsat9377 : Unsatisfiable (PosFin 65) f9377 := by
  apply lratCheckerSound f9377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9377
  · intro a ha; simp [p9377] at ha; subst a; trivial
  · exact checked9377
theorem derived9377 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9377 := by
  apply localUnsat_implies_entails f9377 [c9367, c9228, c9373, c9376, c9369, c6990, c7000, c6987, c6986, c5564] c9377 unsat9377 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9373 := derived9373 a h
  have h3 : Entails.eval a c9376 := derived9376 a h
  have h4 : Entails.eval a c9369 := derived9369 a h
  have h5 : Entails.eval a c6990 := derived6990 a h
  have h6 : Entails.eval a c7000 := derived7000 a h
  have h7 : Entails.eval a c6987 := derived6987 a h
  have h8 : Entails.eval a c6986 := derived6986 a h
  have h9 : Entails.eval a c5564 := h 5563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9378 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨57, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9378 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9373, some c9377, some c6910, some c6981, some c6831, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9378 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9378 : lratChecker f9378 p9378 = .success := by decide +kernel
theorem unsat9378 : Unsatisfiable (PosFin 65) f9378 := by
  apply lratCheckerSound f9378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9378
  · intro a ha; simp [p9378] at ha; subst a; trivial
  · exact checked9378
theorem derived9378 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9378 := by
  apply localUnsat_implies_entails f9378 [c9367, c9373, c9377, c6910, c6981, c6831] c9378 unsat9378 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9373 := derived9373 a h
  have h2 : Entails.eval a c9377 := derived9377 a h
  have h3 : Entails.eval a c6910 := derived6910 a h
  have h4 : Entails.eval a c6981 := derived6981 a h
  have h5 : Entails.eval a c6831 := derived6831 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9379 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨62, by decide⟩, true), (⟨34, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9379 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c6914, some c6985, some c6831, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9379 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9379 : lratChecker f9379 p9379 = .success := by decide +kernel
theorem unsat9379 : Unsatisfiable (PosFin 65) f9379 := by
  apply lratCheckerSound f9379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9379
  · intro a ha; simp [p9379] at ha; subst a; trivial
  · exact checked9379
theorem derived9379 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9379 := by
  apply localUnsat_implies_entails f9379 [c9367, c6914, c6985, c6831] c9379 unsat9379 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c6914 := derived6914 a h
  have h2 : Entails.eval a c6985 := derived6985 a h
  have h3 : Entails.eval a c6831 := derived6831 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9380 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨57, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9380 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c9367, some c9373, some c9376, some c9378, some c9379, some c9369, some c6994, some c6787, some c3722, some c5205, some c6798, some c3594, some c4314, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9380 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9380 : lratChecker f9380 p9380 = .success := by decide +kernel
theorem unsat9380 : Unsatisfiable (PosFin 65) f9380 := by
  apply lratCheckerSound f9380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9380
  · intro a ha; simp [p9380] at ha; subst a; trivial
  · exact checked9380
theorem derived9380 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9380 := by
  apply localUnsat_implies_entails f9380 [c9228, c9229, c9367, c9373, c9376, c9378, c9379, c9369, c6994, c6787, c3722, c5205, c6798, c3594, c4314] c9380 unsat9380 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9367 := derived9367 a h
  have h3 : Entails.eval a c9373 := derived9373 a h
  have h4 : Entails.eval a c9376 := derived9376 a h
  have h5 : Entails.eval a c9378 := derived9378 a h
  have h6 : Entails.eval a c9379 := derived9379 a h
  have h7 : Entails.eval a c9369 := derived9369 a h
  have h8 : Entails.eval a c6994 := derived6994 a h
  have h9 : Entails.eval a c6787 := derived6787 a h
  have h10 : Entails.eval a c3722 := h 3721 (by decide)
  have h11 : Entails.eval a c5205 := h 5204 (by decide)
  have h12 : Entails.eval a c6798 := derived6798 a h
  have h13 : Entails.eval a c3594 := h 3593 (by decide)
  have h14 : Entails.eval a c4314 := h 4313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9380

end CochromaticTwenty.Certificates.FixedCore1
