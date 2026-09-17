import MerLeanExperiment.Certificates.FixedCore0.Steps0600_0699

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8251 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, true), (⟨61, by decide⟩, true), (⟨36, by decide⟩, false), (⟨57, by decide⟩, true), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8251 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2959, some c3114, some c503, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8251 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8251 : lratChecker f8251 p8251 = .success := by decide +kernel
theorem unsat8251 : Unsatisfiable (PosFin 65) f8251 := by
  apply lratCheckerSound f8251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8251
  · intro a ha; simp [p8251] at ha; subst a; trivial
  · exact checked8251
theorem derived8251 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8251 := by
  apply localUnsat_implies_entails f8251 [c2959, c3114, c503] c8251 unsat8251 (by rfl) a
  have h0 : Entails.eval a c2959 := h 2958 (by decide)
  have h1 : Entails.eval a c3114 := h 3113 (by decide)
  have h2 : Entails.eval a c503 := h 502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8252 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨60, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8252 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8237, some c7994, some c8189, some c8211, some c8220, some c8232, some c8233, some c6681, some c6696, some c7257, some c7166, some c6952, some c6307, some c7418, some c8160, some c8249, some c8250, some c8238, some c8251, some c450, some c517, some c2586, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8252 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8252 : lratChecker f8252 p8252 = .success := by decide +kernel
theorem unsat8252 : Unsatisfiable (PosFin 65) f8252 := by
  apply lratCheckerSound f8252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8252
  · intro a ha; simp [p8252] at ha; subst a; trivial
  · exact checked8252
theorem derived8252 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8252 := by
  apply localUnsat_implies_entails f8252 [c8237, c7994, c8189, c8211, c8220, c8232, c8233, c6681, c6696, c7257, c7166, c6952, c6307, c7418, c8160, c8249, c8250, c8238, c8251, c450, c517, c2586] c8252 unsat8252 (by rfl) a
  have h0 : Entails.eval a c8237 := derived8237 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8211 := derived8211 a h
  have h4 : Entails.eval a c8220 := derived8220 a h
  have h5 : Entails.eval a c8232 := derived8232 a h
  have h6 : Entails.eval a c8233 := derived8233 a h
  have h7 : Entails.eval a c6681 := h 6680 (by decide)
  have h8 : Entails.eval a c6696 := h 6695 (by decide)
  have h9 : Entails.eval a c7257 := h 7256 (by decide)
  have h10 : Entails.eval a c7166 := h 7165 (by decide)
  have h11 : Entails.eval a c6952 := h 6951 (by decide)
  have h12 : Entails.eval a c6307 := h 6306 (by decide)
  have h13 : Entails.eval a c7418 := h 7417 (by decide)
  have h14 : Entails.eval a c8160 := derived8160 a h
  have h15 : Entails.eval a c8249 := derived8249 a h
  have h16 : Entails.eval a c8250 := derived8250 a h
  have h17 : Entails.eval a c8238 := derived8238 a h
  have h18 : Entails.eval a c8251 := derived8251 a h
  have h19 : Entails.eval a c450 := h 449 (by decide)
  have h20 : Entails.eval a c517 := h 516 (by decide)
  have h21 : Entails.eval a c2586 := h 2585 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8253 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨37, by decide⟩, false), (⟨34, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8253 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c450, some c517, some c2586, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8253 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8253 : lratChecker f8253 p8253 = .success := by decide +kernel
theorem unsat8253 : Unsatisfiable (PosFin 65) f8253 := by
  apply lratCheckerSound f8253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8253
  · intro a ha; simp [p8253] at ha; subst a; trivial
  · exact checked8253
theorem derived8253 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8253 := by
  apply localUnsat_implies_entails f8253 [c450, c517, c2586] c8253 unsat8253 (by rfl) a
  have h0 : Entails.eval a c450 := h 449 (by decide)
  have h1 : Entails.eval a c517 := h 516 (by decide)
  have h2 : Entails.eval a c2586 := h 2585 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8254 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨34, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8254 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6696, some c6681, some c7257, some c524, some c457, some c2586, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8254 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8254 : lratChecker f8254 p8254 = .success := by decide +kernel
theorem unsat8254 : Unsatisfiable (PosFin 65) f8254 := by
  apply lratCheckerSound f8254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8254
  · intro a ha; simp [p8254] at ha; subst a; trivial
  · exact checked8254
theorem derived8254 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8254 := by
  apply localUnsat_implies_entails f8254 [c6696, c6681, c7257, c524, c457, c2586] c8254 unsat8254 (by rfl) a
  have h0 : Entails.eval a c6696 := h 6695 (by decide)
  have h1 : Entails.eval a c6681 := h 6680 (by decide)
  have h2 : Entails.eval a c7257 := h 7256 (by decide)
  have h3 : Entails.eval a c524 := h 523 (by decide)
  have h4 : Entails.eval a c457 := h 456 (by decide)
  have h5 : Entails.eval a c2586 := h 2585 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8255 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨34, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8255 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6696, some c6681, some c7257, some c8253, some c8254, some c4575, some c1950, some c3117, some c1226, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8255 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8255 : lratChecker f8255 p8255 = .success := by decide +kernel
theorem unsat8255 : Unsatisfiable (PosFin 65) f8255 := by
  apply lratCheckerSound f8255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8255
  · intro a ha; simp [p8255] at ha; subst a; trivial
  · exact checked8255
theorem derived8255 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8255 := by
  apply localUnsat_implies_entails f8255 [c6696, c6681, c7257, c8253, c8254, c4575, c1950, c3117, c1226] c8255 unsat8255 (by rfl) a
  have h0 : Entails.eval a c6696 := h 6695 (by decide)
  have h1 : Entails.eval a c6681 := h 6680 (by decide)
  have h2 : Entails.eval a c7257 := h 7256 (by decide)
  have h3 : Entails.eval a c8253 := derived8253 a h
  have h4 : Entails.eval a c8254 := derived8254 a h
  have h5 : Entails.eval a c4575 := h 4574 (by decide)
  have h6 : Entails.eval a c1950 := h 1949 (by decide)
  have h7 : Entails.eval a c3117 := h 3116 (by decide)
  have h8 : Entails.eval a c1226 := h 1225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8256 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8256 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8160, some c8232, some c8189, some c8211, some c8220, some c8233, some c6696, some c6681, some c7257, some c7166, some c6952, some c6307, some c7418, some c8237, some c8255, some c8250, some c535, some c479, some c8252, some c2964, some c498, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8256 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8256 : lratChecker f8256 p8256 = .success := by decide +kernel
theorem unsat8256 : Unsatisfiable (PosFin 65) f8256 := by
  apply lratCheckerSound f8256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8256
  · intro a ha; simp [p8256] at ha; subst a; trivial
  · exact checked8256
theorem derived8256 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8256 := by
  apply localUnsat_implies_entails f8256 [c7994, c8160, c8232, c8189, c8211, c8220, c8233, c6696, c6681, c7257, c7166, c6952, c6307, c7418, c8237, c8255, c8250, c535, c479, c8252, c2964, c498] c8256 unsat8256 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8232 := derived8232 a h
  have h3 : Entails.eval a c8189 := derived8189 a h
  have h4 : Entails.eval a c8211 := derived8211 a h
  have h5 : Entails.eval a c8220 := derived8220 a h
  have h6 : Entails.eval a c8233 := derived8233 a h
  have h7 : Entails.eval a c6696 := h 6695 (by decide)
  have h8 : Entails.eval a c6681 := h 6680 (by decide)
  have h9 : Entails.eval a c7257 := h 7256 (by decide)
  have h10 : Entails.eval a c7166 := h 7165 (by decide)
  have h11 : Entails.eval a c6952 := h 6951 (by decide)
  have h12 : Entails.eval a c6307 := h 6306 (by decide)
  have h13 : Entails.eval a c7418 := h 7417 (by decide)
  have h14 : Entails.eval a c8237 := derived8237 a h
  have h15 : Entails.eval a c8255 := derived8255 a h
  have h16 : Entails.eval a c8250 := derived8250 a h
  have h17 : Entails.eval a c535 := h 534 (by decide)
  have h18 : Entails.eval a c479 := h 478 (by decide)
  have h19 : Entails.eval a c8252 := derived8252 a h
  have h20 : Entails.eval a c2964 := h 2963 (by decide)
  have h21 : Entails.eval a c498 := h 497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8257 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8257 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8232, some c8220, some c8211, some c8189, some c8160, some c7994, some c8233, some c6696, some c6681, some c7257, some c7166, some c6952, some c6307, some c7418, some c8237, some c8255, some c479, some c535, some c3117, some c8256, some c2960, some c505, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8257 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8257 : lratChecker f8257 p8257 = .success := by decide +kernel
theorem unsat8257 : Unsatisfiable (PosFin 65) f8257 := by
  apply lratCheckerSound f8257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8257
  · intro a ha; simp [p8257] at ha; subst a; trivial
  · exact checked8257
theorem derived8257 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8257 := by
  apply localUnsat_implies_entails f8257 [c8232, c8220, c8211, c8189, c8160, c7994, c8233, c6696, c6681, c7257, c7166, c6952, c6307, c7418, c8237, c8255, c479, c535, c3117, c8256, c2960, c505] c8257 unsat8257 (by rfl) a
  have h0 : Entails.eval a c8232 := derived8232 a h
  have h1 : Entails.eval a c8220 := derived8220 a h
  have h2 : Entails.eval a c8211 := derived8211 a h
  have h3 : Entails.eval a c8189 := derived8189 a h
  have h4 : Entails.eval a c8160 := derived8160 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c8233 := derived8233 a h
  have h7 : Entails.eval a c6696 := h 6695 (by decide)
  have h8 : Entails.eval a c6681 := h 6680 (by decide)
  have h9 : Entails.eval a c7257 := h 7256 (by decide)
  have h10 : Entails.eval a c7166 := h 7165 (by decide)
  have h11 : Entails.eval a c6952 := h 6951 (by decide)
  have h12 : Entails.eval a c6307 := h 6306 (by decide)
  have h13 : Entails.eval a c7418 := h 7417 (by decide)
  have h14 : Entails.eval a c8237 := derived8237 a h
  have h15 : Entails.eval a c8255 := derived8255 a h
  have h16 : Entails.eval a c479 := h 478 (by decide)
  have h17 : Entails.eval a c535 := h 534 (by decide)
  have h18 : Entails.eval a c3117 := h 3116 (by decide)
  have h19 : Entails.eval a c8256 := derived8256 a h
  have h20 : Entails.eval a c2960 := h 2959 (by decide)
  have h21 : Entails.eval a c505 := h 504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8258 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8258 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8220, some c8189, some c8075, some c3122, some c2966, some c3669, some c507, some c2524, some c6623, some c461, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8258 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8258 : lratChecker f8258 p8258 = .success := by decide +kernel
theorem unsat8258 : Unsatisfiable (PosFin 65) f8258 := by
  apply lratCheckerSound f8258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8258
  · intro a ha; simp [p8258] at ha; subst a; trivial
  · exact checked8258
theorem derived8258 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8258 := by
  apply localUnsat_implies_entails f8258 [c8220, c8189, c8075, c3122, c2966, c3669, c507, c2524, c6623, c461] c8258 unsat8258 (by rfl) a
  have h0 : Entails.eval a c8220 := derived8220 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c3122 := h 3121 (by decide)
  have h4 : Entails.eval a c2966 := h 2965 (by decide)
  have h5 : Entails.eval a c3669 := h 3668 (by decide)
  have h6 : Entails.eval a c507 := h 506 (by decide)
  have h7 : Entails.eval a c2524 := h 2523 (by decide)
  have h8 : Entails.eval a c6623 := h 6622 (by decide)
  have h9 : Entails.eval a c461 := h 460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8259 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8259 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8232, some c8220, some c8211, some c8075, some c8258, some c3173, some c3211, some c3844, some c1819, some c426, some c438, some c6571, some c7117, some c6667, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8259 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8259 : lratChecker f8259 p8259 = .success := by decide +kernel
theorem unsat8259 : Unsatisfiable (PosFin 65) f8259 := by
  apply lratCheckerSound f8259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8259
  · intro a ha; simp [p8259] at ha; subst a; trivial
  · exact checked8259
theorem derived8259 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8259 := by
  apply localUnsat_implies_entails f8259 [c8232, c8220, c8211, c8075, c8258, c3173, c3211, c3844, c1819, c426, c438, c6571, c7117, c6667] c8259 unsat8259 (by rfl) a
  have h0 : Entails.eval a c8232 := derived8232 a h
  have h1 : Entails.eval a c8220 := derived8220 a h
  have h2 : Entails.eval a c8211 := derived8211 a h
  have h3 : Entails.eval a c8075 := derived8075 a h
  have h4 : Entails.eval a c8258 := derived8258 a h
  have h5 : Entails.eval a c3173 := h 3172 (by decide)
  have h6 : Entails.eval a c3211 := h 3210 (by decide)
  have h7 : Entails.eval a c3844 := h 3843 (by decide)
  have h8 : Entails.eval a c1819 := h 1818 (by decide)
  have h9 : Entails.eval a c426 := h 425 (by decide)
  have h10 : Entails.eval a c438 := h 437 (by decide)
  have h11 : Entails.eval a c6571 := h 6570 (by decide)
  have h12 : Entails.eval a c7117 := h 7116 (by decide)
  have h13 : Entails.eval a c6667 := h 6666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8260 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8260 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8232, some c8211, some c8189, some c8075, some c8259, some c4316, some c70, some c4356, some c4941, some c4198, some c90, some c4052, some c4100, some c5379, some c2270, some c11, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8260 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8260 : lratChecker f8260 p8260 = .success := by decide +kernel
theorem unsat8260 : Unsatisfiable (PosFin 65) f8260 := by
  apply lratCheckerSound f8260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8260
  · intro a ha; simp [p8260] at ha; subst a; trivial
  · exact checked8260
theorem derived8260 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8260 := by
  apply localUnsat_implies_entails f8260 [c8232, c8211, c8189, c8075, c8259, c4316, c70, c4356, c4941, c4198, c90, c4052, c4100, c5379, c2270, c11] c8260 unsat8260 (by rfl) a
  have h0 : Entails.eval a c8232 := derived8232 a h
  have h1 : Entails.eval a c8211 := derived8211 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8075 := derived8075 a h
  have h4 : Entails.eval a c8259 := derived8259 a h
  have h5 : Entails.eval a c4316 := h 4315 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c4356 := h 4355 (by decide)
  have h8 : Entails.eval a c4941 := h 4940 (by decide)
  have h9 : Entails.eval a c4198 := h 4197 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c4052 := h 4051 (by decide)
  have h12 : Entails.eval a c4100 := h 4099 (by decide)
  have h13 : Entails.eval a c5379 := h 5378 (by decide)
  have h14 : Entails.eval a c2270 := h 2269 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8261 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8261 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8220, some c8189, some c8075, some c5379, some c5391, some c6046, some c6206, some c5343, some c5837, some c5874, some c5767, some c5230, some c5550, some c6623, some c5174, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8261 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8261 : lratChecker f8261 p8261 = .success := by decide +kernel
theorem unsat8261 : Unsatisfiable (PosFin 65) f8261 := by
  apply lratCheckerSound f8261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8261
  · intro a ha; simp [p8261] at ha; subst a; trivial
  · exact checked8261
theorem derived8261 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8261 := by
  apply localUnsat_implies_entails f8261 [c8220, c8189, c8075, c5379, c5391, c6046, c6206, c5343, c5837, c5874, c5767, c5230, c5550, c6623, c5174] c8261 unsat8261 (by rfl) a
  have h0 : Entails.eval a c8220 := derived8220 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c5379 := h 5378 (by decide)
  have h4 : Entails.eval a c5391 := h 5390 (by decide)
  have h5 : Entails.eval a c6046 := h 6045 (by decide)
  have h6 : Entails.eval a c6206 := h 6205 (by decide)
  have h7 : Entails.eval a c5343 := h 5342 (by decide)
  have h8 : Entails.eval a c5837 := h 5836 (by decide)
  have h9 : Entails.eval a c5874 := h 5873 (by decide)
  have h10 : Entails.eval a c5767 := h 5766 (by decide)
  have h11 : Entails.eval a c5230 := h 5229 (by decide)
  have h12 : Entails.eval a c5550 := h 5549 (by decide)
  have h13 : Entails.eval a c6623 := h 6622 (by decide)
  have h14 : Entails.eval a c5174 := h 5173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8262 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨57, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, true), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8262 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1966, some c1533, some c2032, some c4052, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p8262 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8262 : lratChecker f8262 p8262 = .success := by decide +kernel
theorem unsat8262 : Unsatisfiable (PosFin 65) f8262 := by
  apply lratCheckerSound f8262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8262
  · intro a ha; simp [p8262] at ha; subst a; trivial
  · exact checked8262
theorem derived8262 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8262 := by
  apply localUnsat_implies_entails f8262 [c1966, c1533, c2032, c4052] c8262 unsat8262 (by rfl) a
  have h0 : Entails.eval a c1966 := h 1965 (by decide)
  have h1 : Entails.eval a c1533 := h 1532 (by decide)
  have h2 : Entails.eval a c2032 := h 2031 (by decide)
  have h3 : Entails.eval a c4052 := h 4051 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8263 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8263 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8232, some c8220, some c8211, some c8075, some c8260, some c8262, some c11, some c8261, some c70, some c8258, some c1305, some c3533, some c438, some c6623, some c7117, some c6667, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8263 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8263 : lratChecker f8263 p8263 = .success := by decide +kernel
theorem unsat8263 : Unsatisfiable (PosFin 65) f8263 := by
  apply lratCheckerSound f8263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8263
  · intro a ha; simp [p8263] at ha; subst a; trivial
  · exact checked8263
theorem derived8263 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8263 := by
  apply localUnsat_implies_entails f8263 [c8232, c8220, c8211, c8075, c8260, c8262, c11, c8261, c70, c8258, c1305, c3533, c438, c6623, c7117, c6667] c8263 unsat8263 (by rfl) a
  have h0 : Entails.eval a c8232 := derived8232 a h
  have h1 : Entails.eval a c8220 := derived8220 a h
  have h2 : Entails.eval a c8211 := derived8211 a h
  have h3 : Entails.eval a c8075 := derived8075 a h
  have h4 : Entails.eval a c8260 := derived8260 a h
  have h5 : Entails.eval a c8262 := derived8262 a h
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c8261 := derived8261 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c8258 := derived8258 a h
  have h10 : Entails.eval a c1305 := h 1304 (by decide)
  have h11 : Entails.eval a c3533 := h 3532 (by decide)
  have h12 : Entails.eval a c438 := h 437 (by decide)
  have h13 : Entails.eval a c6623 := h 6622 (by decide)
  have h14 : Entails.eval a c7117 := h 7116 (by decide)
  have h15 : Entails.eval a c6667 := h 6666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8264 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8264 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8263, some c8257, some c8232, some c8211, some c8075, some c6647, some c6492, some c7125, some c6632, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8264 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8264 : lratChecker f8264 p8264 = .success := by decide +kernel
theorem unsat8264 : Unsatisfiable (PosFin 65) f8264 := by
  apply lratCheckerSound f8264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8264
  · intro a ha; simp [p8264] at ha; subst a; trivial
  · exact checked8264
theorem derived8264 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8264 := by
  apply localUnsat_implies_entails f8264 [c8263, c8257, c8232, c8211, c8075, c6647, c6492, c7125, c6632] c8264 unsat8264 (by rfl) a
  have h0 : Entails.eval a c8263 := derived8263 a h
  have h1 : Entails.eval a c8257 := derived8257 a h
  have h2 : Entails.eval a c8232 := derived8232 a h
  have h3 : Entails.eval a c8211 := derived8211 a h
  have h4 : Entails.eval a c8075 := derived8075 a h
  have h5 : Entails.eval a c6647 := h 6646 (by decide)
  have h6 : Entails.eval a c6492 := h 6491 (by decide)
  have h7 : Entails.eval a c7125 := h 7124 (by decide)
  have h8 : Entails.eval a c6632 := h 6631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8265 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8265 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8263, some c8257, some c8232, some c8222, some c8264, some c7386, some c7280, some c7267, some c7219, some c8189, some c5417, some c5336, some c5243, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8265 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8265 : lratChecker f8265 p8265 = .success := by decide +kernel
theorem unsat8265 : Unsatisfiable (PosFin 65) f8265 := by
  apply lratCheckerSound f8265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8265
  · intro a ha; simp [p8265] at ha; subst a; trivial
  · exact checked8265
theorem derived8265 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8265 := by
  apply localUnsat_implies_entails f8265 [c8075, c8263, c8257, c8232, c8222, c8264, c7386, c7280, c7267, c7219, c8189, c5417, c5336, c5243] c8265 unsat8265 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8263 := derived8263 a h
  have h2 : Entails.eval a c8257 := derived8257 a h
  have h3 : Entails.eval a c8232 := derived8232 a h
  have h4 : Entails.eval a c8222 := derived8222 a h
  have h5 : Entails.eval a c8264 := derived8264 a h
  have h6 : Entails.eval a c7386 := h 7385 (by decide)
  have h7 : Entails.eval a c7280 := h 7279 (by decide)
  have h8 : Entails.eval a c7267 := h 7266 (by decide)
  have h9 : Entails.eval a c7219 := h 7218 (by decide)
  have h10 : Entails.eval a c8189 := derived8189 a h
  have h11 : Entails.eval a c5417 := h 5416 (by decide)
  have h12 : Entails.eval a c5336 := h 5335 (by decide)
  have h13 : Entails.eval a c5243 := h 5242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8266 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8266 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3114, some c3118, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8266 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8266 : lratChecker f8266 p8266 = .success := by decide +kernel
theorem unsat8266 : Unsatisfiable (PosFin 65) f8266 := by
  apply lratCheckerSound f8266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8266
  · intro a ha; simp [p8266] at ha; subst a; trivial
  · exact checked8266
theorem derived8266 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8266 := by
  apply localUnsat_implies_entails f8266 [c3114, c3118] c8266 unsat8266 (by rfl) a
  have h0 : Entails.eval a c3114 := h 3113 (by decide)
  have h1 : Entails.eval a c3118 := h 3117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8267 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8267 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8263, some c8257, some c8075, some c8232, some c8222, some c8264, some c7386, some c7280, some c7267, some c7219, some c7139, some c8223, some c8220, some c6750, some c8211, some c8189, some c8160, some c9, some c8265, some c5253, some c411, some c422, some c5376, some c2482, some c2513, some c88, some c8266, some c4400, some c4423, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8267 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked8267 : lratChecker f8267 p8267 = .success := by decide +kernel
theorem unsat8267 : Unsatisfiable (PosFin 65) f8267 := by
  apply lratCheckerSound f8267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8267
  · intro a ha; simp [p8267] at ha; subst a; trivial
  · exact checked8267
theorem derived8267 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8267 := by
  apply localUnsat_implies_entails f8267 [c8263, c8257, c8075, c8232, c8222, c8264, c7386, c7280, c7267, c7219, c7139, c8223, c8220, c6750, c8211, c8189, c8160, c9, c8265, c5253, c411, c422, c5376, c2482, c2513, c88, c8266, c4400, c4423] c8267 unsat8267 (by rfl) a
  have h0 : Entails.eval a c8263 := derived8263 a h
  have h1 : Entails.eval a c8257 := derived8257 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c8232 := derived8232 a h
  have h4 : Entails.eval a c8222 := derived8222 a h
  have h5 : Entails.eval a c8264 := derived8264 a h
  have h6 : Entails.eval a c7386 := h 7385 (by decide)
  have h7 : Entails.eval a c7280 := h 7279 (by decide)
  have h8 : Entails.eval a c7267 := h 7266 (by decide)
  have h9 : Entails.eval a c7219 := h 7218 (by decide)
  have h10 : Entails.eval a c7139 := h 7138 (by decide)
  have h11 : Entails.eval a c8223 := derived8223 a h
  have h12 : Entails.eval a c8220 := derived8220 a h
  have h13 : Entails.eval a c6750 := h 6749 (by decide)
  have h14 : Entails.eval a c8211 := derived8211 a h
  have h15 : Entails.eval a c8189 := derived8189 a h
  have h16 : Entails.eval a c8160 := derived8160 a h
  have h17 : Entails.eval a c9 := h 8 (by decide)
  have h18 : Entails.eval a c8265 := derived8265 a h
  have h19 : Entails.eval a c5253 := h 5252 (by decide)
  have h20 : Entails.eval a c411 := h 410 (by decide)
  have h21 : Entails.eval a c422 := h 421 (by decide)
  have h22 : Entails.eval a c5376 := h 5375 (by decide)
  have h23 : Entails.eval a c2482 := h 2481 (by decide)
  have h24 : Entails.eval a c2513 := h 2512 (by decide)
  have h25 : Entails.eval a c88 := h 87 (by decide)
  have h26 : Entails.eval a c8266 := derived8266 a h
  have h27 : Entails.eval a c4400 := h 4399 (by decide)
  have h28 : Entails.eval a c4423 := h 4422 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8268 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8268 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8267, some c8263, some c8257, some c8222, some c8075, some c8264, some c7386, some c8232, some c1743, some c1952, some c536, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8268 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8268 : lratChecker f8268 p8268 = .success := by decide +kernel
theorem unsat8268 : Unsatisfiable (PosFin 65) f8268 := by
  apply lratCheckerSound f8268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8268
  · intro a ha; simp [p8268] at ha; subst a; trivial
  · exact checked8268
theorem derived8268 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8268 := by
  apply localUnsat_implies_entails f8268 [c8267, c8263, c8257, c8222, c8075, c8264, c7386, c8232, c1743, c1952, c536] c8268 unsat8268 (by rfl) a
  have h0 : Entails.eval a c8267 := derived8267 a h
  have h1 : Entails.eval a c8263 := derived8263 a h
  have h2 : Entails.eval a c8257 := derived8257 a h
  have h3 : Entails.eval a c8222 := derived8222 a h
  have h4 : Entails.eval a c8075 := derived8075 a h
  have h5 : Entails.eval a c8264 := derived8264 a h
  have h6 : Entails.eval a c7386 := h 7385 (by decide)
  have h7 : Entails.eval a c8232 := derived8232 a h
  have h8 : Entails.eval a c1743 := h 1742 (by decide)
  have h9 : Entails.eval a c1952 := h 1951 (by decide)
  have h10 : Entails.eval a c536 := h 535 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8269 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8269 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8189, some c8220, some c8232, some c8263, some c8257, some c8222, some c8264, some c7386, some c7280, some c7267, some c7219, some c7139, some c6750, some c8267, some c8268, some c525, some c458, some c1580, some c1520, some c2600, some c4350, some c4686, some c1805, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8269 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked8269 : lratChecker f8269 p8269 = .success := by decide +kernel
theorem unsat8269 : Unsatisfiable (PosFin 65) f8269 := by
  apply lratCheckerSound f8269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8269
  · intro a ha; simp [p8269] at ha; subst a; trivial
  · exact checked8269
theorem derived8269 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8269 := by
  apply localUnsat_implies_entails f8269 [c8075, c8189, c8220, c8232, c8263, c8257, c8222, c8264, c7386, c7280, c7267, c7219, c7139, c6750, c8267, c8268, c525, c458, c1580, c1520, c2600, c4350, c4686, c1805] c8269 unsat8269 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c8220 := derived8220 a h
  have h3 : Entails.eval a c8232 := derived8232 a h
  have h4 : Entails.eval a c8263 := derived8263 a h
  have h5 : Entails.eval a c8257 := derived8257 a h
  have h6 : Entails.eval a c8222 := derived8222 a h
  have h7 : Entails.eval a c8264 := derived8264 a h
  have h8 : Entails.eval a c7386 := h 7385 (by decide)
  have h9 : Entails.eval a c7280 := h 7279 (by decide)
  have h10 : Entails.eval a c7267 := h 7266 (by decide)
  have h11 : Entails.eval a c7219 := h 7218 (by decide)
  have h12 : Entails.eval a c7139 := h 7138 (by decide)
  have h13 : Entails.eval a c6750 := h 6749 (by decide)
  have h14 : Entails.eval a c8267 := derived8267 a h
  have h15 : Entails.eval a c8268 := derived8268 a h
  have h16 : Entails.eval a c525 := h 524 (by decide)
  have h17 : Entails.eval a c458 := h 457 (by decide)
  have h18 : Entails.eval a c1580 := h 1579 (by decide)
  have h19 : Entails.eval a c1520 := h 1519 (by decide)
  have h20 : Entails.eval a c2600 := h 2599 (by decide)
  have h21 : Entails.eval a c4350 := h 4349 (by decide)
  have h22 : Entails.eval a c4686 := h 4685 (by decide)
  have h23 : Entails.eval a c1805 := h 1804 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8270 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨64, by decide⟩, false), (⟨52, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8270 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7360, some c7139, some c7304, some c7219, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p8270 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8270 : lratChecker f8270 p8270 = .success := by decide +kernel
theorem unsat8270 : Unsatisfiable (PosFin 65) f8270 := by
  apply lratCheckerSound f8270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8270
  · intro a ha; simp [p8270] at ha; subst a; trivial
  · exact checked8270
theorem derived8270 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8270 := by
  apply localUnsat_implies_entails f8270 [c7360, c7139, c7304, c7219] c8270 unsat8270 (by rfl) a
  have h0 : Entails.eval a c7360 := h 7359 (by decide)
  have h1 : Entails.eval a c7139 := h 7138 (by decide)
  have h2 : Entails.eval a c7304 := h 7303 (by decide)
  have h3 : Entails.eval a c7219 := h 7218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8271 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨38, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8271 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7219, some c6632, some c6658, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8271 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8271 : lratChecker f8271 p8271 = .success := by decide +kernel
theorem unsat8271 : Unsatisfiable (PosFin 65) f8271 := by
  apply lratCheckerSound f8271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8271
  · intro a ha; simp [p8271] at ha; subst a; trivial
  · exact checked8271
theorem derived8271 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8271 := by
  apply localUnsat_implies_entails f8271 [c7219, c6632, c6658] c8271 unsat8271 (by rfl) a
  have h0 : Entails.eval a c7219 := h 7218 (by decide)
  have h1 : Entails.eval a c6632 := h 6631 (by decide)
  have h2 : Entails.eval a c6658 := h 6657 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8272 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8272 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8270, some c7295, some c7267, some c7394, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8272 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8272 : lratChecker f8272 p8272 = .success := by decide +kernel
theorem unsat8272 : Unsatisfiable (PosFin 65) f8272 := by
  apply lratCheckerSound f8272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8272
  · intro a ha; simp [p8272] at ha; subst a; trivial
  · exact checked8272
theorem derived8272 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8272 := by
  apply localUnsat_implies_entails f8272 [c8270, c7295, c7267, c7394] c8272 unsat8272 (by rfl) a
  have h0 : Entails.eval a c8270 := derived8270 a h
  have h1 : Entails.eval a c7295 := h 7294 (by decide)
  have h2 : Entails.eval a c7267 := h 7266 (by decide)
  have h3 : Entails.eval a c7394 := h 7393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8273 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8273 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1743, some c1805, some c525, some c458, some c1520, some c2600, some c4686, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8273 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8273 : lratChecker f8273 p8273 = .success := by decide +kernel
theorem unsat8273 : Unsatisfiable (PosFin 65) f8273 := by
  apply lratCheckerSound f8273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8273
  · intro a ha; simp [p8273] at ha; subst a; trivial
  · exact checked8273
theorem derived8273 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8273 := by
  apply localUnsat_implies_entails f8273 [c1743, c1805, c525, c458, c1520, c2600, c4686] c8273 unsat8273 (by rfl) a
  have h0 : Entails.eval a c1743 := h 1742 (by decide)
  have h1 : Entails.eval a c1805 := h 1804 (by decide)
  have h2 : Entails.eval a c525 := h 524 (by decide)
  have h3 : Entails.eval a c458 := h 457 (by decide)
  have h4 : Entails.eval a c1520 := h 1519 (by decide)
  have h5 : Entails.eval a c2600 := h 2599 (by decide)
  have h6 : Entails.eval a c4686 := h 4685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8274 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨1, by decide⟩, true), (⟨38, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8274 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8270, some c8272, some c8271, some c7125, some c7394, some c536, some c518, some c1520, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8274 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8274 : lratChecker f8274 p8274 = .success := by decide +kernel
theorem unsat8274 : Unsatisfiable (PosFin 65) f8274 := by
  apply lratCheckerSound f8274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8274
  · intro a ha; simp [p8274] at ha; subst a; trivial
  · exact checked8274
theorem derived8274 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8274 := by
  apply localUnsat_implies_entails f8274 [c8270, c8272, c8271, c7125, c7394, c536, c518, c1520] c8274 unsat8274 (by rfl) a
  have h0 : Entails.eval a c8270 := derived8270 a h
  have h1 : Entails.eval a c8272 := derived8272 a h
  have h2 : Entails.eval a c8271 := derived8271 a h
  have h3 : Entails.eval a c7125 := h 7124 (by decide)
  have h4 : Entails.eval a c7394 := h 7393 (by decide)
  have h5 : Entails.eval a c536 := h 535 (by decide)
  have h6 : Entails.eval a c518 := h 517 (by decide)
  have h7 : Entails.eval a c1520 := h 1519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8275 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨38, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8275 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8270, some c8272, some c8271, some c7125, some c6911, some c6820, some c6520, some c7394, some c7280, some c8158, some c6750, some c8274, some c8273, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8275 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8275 : lratChecker f8275 p8275 = .success := by decide +kernel
theorem unsat8275 : Unsatisfiable (PosFin 65) f8275 := by
  apply lratCheckerSound f8275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8275
  · intro a ha; simp [p8275] at ha; subst a; trivial
  · exact checked8275
theorem derived8275 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8275 := by
  apply localUnsat_implies_entails f8275 [c8270, c8272, c8271, c7125, c6911, c6820, c6520, c7394, c7280, c8158, c6750, c8274, c8273] c8275 unsat8275 (by rfl) a
  have h0 : Entails.eval a c8270 := derived8270 a h
  have h1 : Entails.eval a c8272 := derived8272 a h
  have h2 : Entails.eval a c8271 := derived8271 a h
  have h3 : Entails.eval a c7125 := h 7124 (by decide)
  have h4 : Entails.eval a c6911 := h 6910 (by decide)
  have h5 : Entails.eval a c6820 := h 6819 (by decide)
  have h6 : Entails.eval a c6520 := h 6519 (by decide)
  have h7 : Entails.eval a c7394 := h 7393 (by decide)
  have h8 : Entails.eval a c7280 := h 7279 (by decide)
  have h9 : Entails.eval a c8158 := derived8158 a h
  have h10 : Entails.eval a c6750 := h 6749 (by decide)
  have h11 : Entails.eval a c8274 := derived8274 a h
  have h12 : Entails.eval a c8273 := derived8273 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8276 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8276 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8270, some c8272, some c8271, some c7125, some c6911, some c7394, some c6820, some c7280, some c6520, some c6750, some c8158, some c8275, some c422, some c411, some c9, some c2482, some c2111, some c2178, some c3253, some c4634, some c88, some c80, some c5417, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p8276 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8276 : lratChecker f8276 p8276 = .success := by decide +kernel
theorem unsat8276 : Unsatisfiable (PosFin 65) f8276 := by
  apply lratCheckerSound f8276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8276
  · intro a ha; simp [p8276] at ha; subst a; trivial
  · exact checked8276
theorem derived8276 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8276 := by
  apply localUnsat_implies_entails f8276 [c8270, c8272, c8271, c7125, c6911, c7394, c6820, c7280, c6520, c6750, c8158, c8275, c422, c411, c9, c2482, c2111, c2178, c3253, c4634, c88, c80, c5417] c8276 unsat8276 (by rfl) a
  have h0 : Entails.eval a c8270 := derived8270 a h
  have h1 : Entails.eval a c8272 := derived8272 a h
  have h2 : Entails.eval a c8271 := derived8271 a h
  have h3 : Entails.eval a c7125 := h 7124 (by decide)
  have h4 : Entails.eval a c6911 := h 6910 (by decide)
  have h5 : Entails.eval a c7394 := h 7393 (by decide)
  have h6 : Entails.eval a c6820 := h 6819 (by decide)
  have h7 : Entails.eval a c7280 := h 7279 (by decide)
  have h8 : Entails.eval a c6520 := h 6519 (by decide)
  have h9 : Entails.eval a c6750 := h 6749 (by decide)
  have h10 : Entails.eval a c8158 := derived8158 a h
  have h11 : Entails.eval a c8275 := derived8275 a h
  have h12 : Entails.eval a c422 := h 421 (by decide)
  have h13 : Entails.eval a c411 := h 410 (by decide)
  have h14 : Entails.eval a c9 := h 8 (by decide)
  have h15 : Entails.eval a c2482 := h 2481 (by decide)
  have h16 : Entails.eval a c2111 := h 2110 (by decide)
  have h17 : Entails.eval a c2178 := h 2177 (by decide)
  have h18 : Entails.eval a c3253 := h 3252 (by decide)
  have h19 : Entails.eval a c4634 := h 4633 (by decide)
  have h20 : Entails.eval a c88 := h 87 (by decide)
  have h21 : Entails.eval a c80 := h 79 (by decide)
  have h22 : Entails.eval a c5417 := h 5416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8277 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8277 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7182, some c7167, some c6520, some c6278, some c9, some c411, some c6911, some c7394, some c422, some c2482, some c2111, some c2178, some c3253, some c4634, some c88, some c80, some c5417, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8277 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8277 : lratChecker f8277 p8277 = .success := by decide +kernel
theorem unsat8277 : Unsatisfiable (PosFin 65) f8277 := by
  apply lratCheckerSound f8277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8277
  · intro a ha; simp [p8277] at ha; subst a; trivial
  · exact checked8277
theorem derived8277 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8277 := by
  apply localUnsat_implies_entails f8277 [c7182, c7167, c6520, c6278, c9, c411, c6911, c7394, c422, c2482, c2111, c2178, c3253, c4634, c88, c80, c5417] c8277 unsat8277 (by rfl) a
  have h0 : Entails.eval a c7182 := h 7181 (by decide)
  have h1 : Entails.eval a c7167 := h 7166 (by decide)
  have h2 : Entails.eval a c6520 := h 6519 (by decide)
  have h3 : Entails.eval a c6278 := h 6277 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c411 := h 410 (by decide)
  have h6 : Entails.eval a c6911 := h 6910 (by decide)
  have h7 : Entails.eval a c7394 := h 7393 (by decide)
  have h8 : Entails.eval a c422 := h 421 (by decide)
  have h9 : Entails.eval a c2482 := h 2481 (by decide)
  have h10 : Entails.eval a c2111 := h 2110 (by decide)
  have h11 : Entails.eval a c2178 := h 2177 (by decide)
  have h12 : Entails.eval a c3253 := h 3252 (by decide)
  have h13 : Entails.eval a c4634 := h 4633 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c80 := h 79 (by decide)
  have h16 : Entails.eval a c5417 := h 5416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8278 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8278 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8276, some c6411, some c6834, some c6278, some c8158, some c7367, some c6863, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8278 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8278 : lratChecker f8278 p8278 = .success := by decide +kernel
theorem unsat8278 : Unsatisfiable (PosFin 65) f8278 := by
  apply lratCheckerSound f8278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8278
  · intro a ha; simp [p8278] at ha; subst a; trivial
  · exact checked8278
theorem derived8278 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8278 := by
  apply localUnsat_implies_entails f8278 [c8276, c6411, c6834, c6278, c8158, c7367, c6863] c8278 unsat8278 (by rfl) a
  have h0 : Entails.eval a c8276 := derived8276 a h
  have h1 : Entails.eval a c6411 := h 6410 (by decide)
  have h2 : Entails.eval a c6834 := h 6833 (by decide)
  have h3 : Entails.eval a c6278 := h 6277 (by decide)
  have h4 : Entails.eval a c8158 := derived8158 a h
  have h5 : Entails.eval a c7367 := h 7366 (by decide)
  have h6 : Entails.eval a c6863 := h 6862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8279 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨39, by decide⟩, false), (⟨35, by decide⟩, false), (⟨6, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8279 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8278, some c480, some c4309, some c2482, some c3289, some c458, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8279 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8279 : lratChecker f8279 p8279 = .success := by decide +kernel
theorem unsat8279 : Unsatisfiable (PosFin 65) f8279 := by
  apply lratCheckerSound f8279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8279
  · intro a ha; simp [p8279] at ha; subst a; trivial
  · exact checked8279
theorem derived8279 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8279 := by
  apply localUnsat_implies_entails f8279 [c8278, c480, c4309, c2482, c3289, c458] c8279 unsat8279 (by rfl) a
  have h0 : Entails.eval a c8278 := derived8278 a h
  have h1 : Entails.eval a c480 := h 479 (by decide)
  have h2 : Entails.eval a c4309 := h 4308 (by decide)
  have h3 : Entails.eval a c2482 := h 2481 (by decide)
  have h4 : Entails.eval a c3289 := h 3288 (by decide)
  have h5 : Entails.eval a c458 := h 457 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8280 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8280 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8276, some c8278, some c7182, some c7167, some c6682, some c8277, some c6520, some c8273, some c6278, some c6911, some c7394, some c6863, some c8279, some c8130, some c2019, some c1520, some c8262, some c8221, some c3939, some c3938, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8280 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8280 : lratChecker f8280 p8280 = .success := by decide +kernel
theorem unsat8280 : Unsatisfiable (PosFin 65) f8280 := by
  apply lratCheckerSound f8280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8280
  · intro a ha; simp [p8280] at ha; subst a; trivial
  · exact checked8280
theorem derived8280 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8280 := by
  apply localUnsat_implies_entails f8280 [c8276, c8278, c7182, c7167, c6682, c8277, c6520, c8273, c6278, c6911, c7394, c6863, c8279, c8130, c2019, c1520, c8262, c8221, c3939, c3938] c8280 unsat8280 (by rfl) a
  have h0 : Entails.eval a c8276 := derived8276 a h
  have h1 : Entails.eval a c8278 := derived8278 a h
  have h2 : Entails.eval a c7182 := h 7181 (by decide)
  have h3 : Entails.eval a c7167 := h 7166 (by decide)
  have h4 : Entails.eval a c6682 := h 6681 (by decide)
  have h5 : Entails.eval a c8277 := derived8277 a h
  have h6 : Entails.eval a c6520 := h 6519 (by decide)
  have h7 : Entails.eval a c8273 := derived8273 a h
  have h8 : Entails.eval a c6278 := h 6277 (by decide)
  have h9 : Entails.eval a c6911 := h 6910 (by decide)
  have h10 : Entails.eval a c7394 := h 7393 (by decide)
  have h11 : Entails.eval a c6863 := h 6862 (by decide)
  have h12 : Entails.eval a c8279 := derived8279 a h
  have h13 : Entails.eval a c8130 := derived8130 a h
  have h14 : Entails.eval a c2019 := h 2018 (by decide)
  have h15 : Entails.eval a c1520 := h 1519 (by decide)
  have h16 : Entails.eval a c8262 := derived8262 a h
  have h17 : Entails.eval a c8221 := derived8221 a h
  have h18 : Entails.eval a c3939 := h 3938 (by decide)
  have h19 : Entails.eval a c3938 := h 3937 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8281 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8281 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8280, some c7182, some c7167, some c6750, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8281 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8281 : lratChecker f8281 p8281 = .success := by decide +kernel
theorem unsat8281 : Unsatisfiable (PosFin 65) f8281 := by
  apply lratCheckerSound f8281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8281
  · intro a ha; simp [p8281] at ha; subst a; trivial
  · exact checked8281
theorem derived8281 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8281 := by
  apply localUnsat_implies_entails f8281 [c8280, c7182, c7167, c6750] c8281 unsat8281 (by rfl) a
  have h0 : Entails.eval a c8280 := derived8280 a h
  have h1 : Entails.eval a c7182 := h 7181 (by decide)
  have h2 : Entails.eval a c7167 := h 7166 (by decide)
  have h3 : Entails.eval a c6750 := h 6749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8282 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨55, by decide⟩, true), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨44, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8282 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7421, some c8182, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8282 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8282 : lratChecker f8282 p8282 = .success := by decide +kernel
theorem unsat8282 : Unsatisfiable (PosFin 65) f8282 := by
  apply lratCheckerSound f8282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8282
  · intro a ha; simp [p8282] at ha; subst a; trivial
  · exact checked8282
theorem derived8282 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8282 := by
  apply localUnsat_implies_entails f8282 [c7421, c8182] c8282 unsat8282 (by rfl) a
  have h0 : Entails.eval a c7421 := h 7420 (by decide)
  have h1 : Entails.eval a c8182 := derived8182 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8283 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨39, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8283 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7410, some c6803, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8283 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8283 : lratChecker f8283 p8283 = .success := by decide +kernel
theorem unsat8283 : Unsatisfiable (PosFin 65) f8283 := by
  apply lratCheckerSound f8283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8283
  · intro a ha; simp [p8283] at ha; subst a; trivial
  · exact checked8283
theorem derived8283 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8283 := by
  apply localUnsat_implies_entails f8283 [c8269, c7410, c6803] c8283 unsat8283 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7410 := h 7409 (by decide)
  have h2 : Entails.eval a c6803 := h 6802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8284 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8284 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8276, some c8269, some c7994, some c8280, some c8281, some c6411, some c6834, some c6321, some c8158, some c6820, some c6863, some c6750, some c8159, some c8283, some c8282, some c7411, some c6799, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8284 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8284 : lratChecker f8284 p8284 = .success := by decide +kernel
theorem unsat8284 : Unsatisfiable (PosFin 65) f8284 := by
  apply lratCheckerSound f8284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8284
  · intro a ha; simp [p8284] at ha; subst a; trivial
  · exact checked8284
theorem derived8284 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8284 := by
  apply localUnsat_implies_entails f8284 [c8276, c8269, c7994, c8280, c8281, c6411, c6834, c6321, c8158, c6820, c6863, c6750, c8159, c8283, c8282, c7411, c6799] c8284 unsat8284 (by rfl) a
  have h0 : Entails.eval a c8276 := derived8276 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8280 := derived8280 a h
  have h4 : Entails.eval a c8281 := derived8281 a h
  have h5 : Entails.eval a c6411 := h 6410 (by decide)
  have h6 : Entails.eval a c6834 := h 6833 (by decide)
  have h7 : Entails.eval a c6321 := h 6320 (by decide)
  have h8 : Entails.eval a c8158 := derived8158 a h
  have h9 : Entails.eval a c6820 := h 6819 (by decide)
  have h10 : Entails.eval a c6863 := h 6862 (by decide)
  have h11 : Entails.eval a c6750 := h 6749 (by decide)
  have h12 : Entails.eval a c8159 := derived8159 a h
  have h13 : Entails.eval a c8283 := derived8283 a h
  have h14 : Entails.eval a c8282 := derived8282 a h
  have h15 : Entails.eval a c7411 := h 7410 (by decide)
  have h16 : Entails.eval a c6799 := h 6798 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8285 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8285 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8284, some c8276, some c6411, some c8278, some c8158, some c6628, some c6863, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8285 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8285 : lratChecker f8285 p8285 = .success := by decide +kernel
theorem unsat8285 : Unsatisfiable (PosFin 65) f8285 := by
  apply lratCheckerSound f8285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8285
  · intro a ha; simp [p8285] at ha; subst a; trivial
  · exact checked8285
theorem derived8285 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8285 := by
  apply localUnsat_implies_entails f8285 [c8284, c8276, c6411, c8278, c8158, c6628, c6863] c8285 unsat8285 (by rfl) a
  have h0 : Entails.eval a c8284 := derived8284 a h
  have h1 : Entails.eval a c8276 := derived8276 a h
  have h2 : Entails.eval a c6411 := h 6410 (by decide)
  have h3 : Entails.eval a c8278 := derived8278 a h
  have h4 : Entails.eval a c8158 := derived8158 a h
  have h5 : Entails.eval a c6628 := h 6627 (by decide)
  have h6 : Entails.eval a c6863 := h 6862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8286 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨33, by decide⟩, false), (⟨46, by decide⟩, true), (⟨35, by decide⟩, false), (⟨38, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8286 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7325, some c6302, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8286 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8286 : lratChecker f8286 p8286 = .success := by decide +kernel
theorem unsat8286 : Unsatisfiable (PosFin 65) f8286 := by
  apply lratCheckerSound f8286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8286
  · intro a ha; simp [p8286] at ha; subst a; trivial
  · exact checked8286
theorem derived8286 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8286 := by
  apply localUnsat_implies_entails f8286 [c8269, c7325, c6302] c8286 unsat8286 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7325 := h 7324 (by decide)
  have h2 : Entails.eval a c6302 := h 6301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8287 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨57, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8287 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6311, some c6306, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8287 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8287 : lratChecker f8287 p8287 = .success := by decide +kernel
theorem unsat8287 : Unsatisfiable (PosFin 65) f8287 := by
  apply lratCheckerSound f8287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8287
  · intro a ha; simp [p8287] at ha; subst a; trivial
  · exact checked8287
theorem derived8287 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8287 := by
  apply localUnsat_implies_entails f8287 [c7994, c6311, c6306] c8287 unsat8287 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6311 := h 6310 (by decide)
  have h2 : Entails.eval a c6306 := h 6305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8288 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8288 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8276, some c7994, some c6863, some c6852, some c6550, some c6321, some c8286, some c8287, some c7318, some c7313, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8288 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8288 : lratChecker f8288 p8288 = .success := by decide +kernel
theorem unsat8288 : Unsatisfiable (PosFin 65) f8288 := by
  apply lratCheckerSound f8288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8288
  · intro a ha; simp [p8288] at ha; subst a; trivial
  · exact checked8288
theorem derived8288 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8288 := by
  apply localUnsat_implies_entails f8288 [c8276, c7994, c6863, c6852, c6550, c6321, c8286, c8287, c7318, c7313] c8288 unsat8288 (by rfl) a
  have h0 : Entails.eval a c8276 := derived8276 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c6863 := h 6862 (by decide)
  have h3 : Entails.eval a c6852 := h 6851 (by decide)
  have h4 : Entails.eval a c6550 := h 6549 (by decide)
  have h5 : Entails.eval a c6321 := h 6320 (by decide)
  have h6 : Entails.eval a c8286 := derived8286 a h
  have h7 : Entails.eval a c8287 := derived8287 a h
  have h8 : Entails.eval a c7318 := h 7317 (by decide)
  have h9 : Entails.eval a c7313 := h 7312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8289 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8289 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8284, some c8285, some c8288, some c7152, some c6628, some c6682, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8289 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8289 : lratChecker f8289 p8289 = .success := by decide +kernel
theorem unsat8289 : Unsatisfiable (PosFin 65) f8289 := by
  apply lratCheckerSound f8289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8289
  · intro a ha; simp [p8289] at ha; subst a; trivial
  · exact checked8289
theorem derived8289 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8289 := by
  apply localUnsat_implies_entails f8289 [c8284, c8285, c8288, c7152, c6628, c6682] c8289 unsat8289 (by rfl) a
  have h0 : Entails.eval a c8284 := derived8284 a h
  have h1 : Entails.eval a c8285 := derived8285 a h
  have h2 : Entails.eval a c8288 := derived8288 a h
  have h3 : Entails.eval a c7152 := h 7151 (by decide)
  have h4 : Entails.eval a c6628 := h 6627 (by decide)
  have h5 : Entails.eval a c6682 := h 6681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8290 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8290 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8276, some c8289, some c6834, some c8284, some c7152, some c6628, some c6682, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8290 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8290 : lratChecker f8290 p8290 = .success := by decide +kernel
theorem unsat8290 : Unsatisfiable (PosFin 65) f8290 := by
  apply lratCheckerSound f8290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8290
  · intro a ha; simp [p8290] at ha; subst a; trivial
  · exact checked8290
theorem derived8290 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8290 := by
  apply localUnsat_implies_entails f8290 [c8276, c8289, c6834, c8284, c7152, c6628, c6682] c8290 unsat8290 (by rfl) a
  have h0 : Entails.eval a c8276 := derived8276 a h
  have h1 : Entails.eval a c8289 := derived8289 a h
  have h2 : Entails.eval a c6834 := h 6833 (by decide)
  have h3 : Entails.eval a c8284 := derived8284 a h
  have h4 : Entails.eval a c7152 := h 7151 (by decide)
  have h5 : Entails.eval a c6628 := h 6627 (by decide)
  have h6 : Entails.eval a c6682 := h 6681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8291 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8291 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7487, some c6682, some c7498, some c6750, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p8291 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8291 : lratChecker f8291 p8291 = .success := by decide +kernel
theorem unsat8291 : Unsatisfiable (PosFin 65) f8291 := by
  apply lratCheckerSound f8291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8291
  · intro a ha; simp [p8291] at ha; subst a; trivial
  · exact checked8291
theorem derived8291 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8291 := by
  apply localUnsat_implies_entails f8291 [c7487, c6682, c7498, c6750] c8291 unsat8291 (by rfl) a
  have h0 : Entails.eval a c7487 := h 7486 (by decide)
  have h1 : Entails.eval a c6682 := h 6681 (by decide)
  have h2 : Entails.eval a c7498 := h 7497 (by decide)
  have h3 : Entails.eval a c6750 := h 6749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8292 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨41, by decide⟩, true), (⟨33, by decide⟩, false), (⟨42, by decide⟩, false), (⟨35, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8292 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6331, some c6783, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8292 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8292 : lratChecker f8292 p8292 = .success := by decide +kernel
theorem unsat8292 : Unsatisfiable (PosFin 65) f8292 := by
  apply lratCheckerSound f8292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8292
  · intro a ha; simp [p8292] at ha; subst a; trivial
  · exact checked8292
theorem derived8292 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8292 := by
  apply localUnsat_implies_entails f8292 [c8269, c6331, c6783] c8292 unsat8292 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6331 := h 6330 (by decide)
  have h2 : Entails.eval a c6783 := h 6782 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8293 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨56, by decide⟩, true), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨37, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8293 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6967, some c7259, some c7021, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8293 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8293 : lratChecker f8293 p8293 = .success := by decide +kernel
theorem unsat8293 : Unsatisfiable (PosFin 65) f8293 := by
  apply lratCheckerSound f8293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8293
  · intro a ha; simp [p8293] at ha; subst a; trivial
  · exact checked8293
theorem derived8293 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8293 := by
  apply localUnsat_implies_entails f8293 [c6967, c7259, c7021] c8293 unsat8293 (by rfl) a
  have h0 : Entails.eval a c6967 := h 6966 (by decide)
  have h1 : Entails.eval a c7259 := h 7258 (by decide)
  have h2 : Entails.eval a c7021 := h 7020 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8294 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8294 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8276, some c8289, some c6834, some c8291, some c8290, some c8284, some c8269, some c7994, some c7402, some c6426, some c6492, some c8292, some c8293, some c7325, some c6347, some c6771, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8294 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8294 : lratChecker f8294 p8294 = .success := by decide +kernel
theorem unsat8294 : Unsatisfiable (PosFin 65) f8294 := by
  apply lratCheckerSound f8294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8294
  · intro a ha; simp [p8294] at ha; subst a; trivial
  · exact checked8294
theorem derived8294 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8294 := by
  apply localUnsat_implies_entails f8294 [c8276, c8289, c6834, c8291, c8290, c8284, c8269, c7994, c7402, c6426, c6492, c8292, c8293, c7325, c6347, c6771] c8294 unsat8294 (by rfl) a
  have h0 : Entails.eval a c8276 := derived8276 a h
  have h1 : Entails.eval a c8289 := derived8289 a h
  have h2 : Entails.eval a c6834 := h 6833 (by decide)
  have h3 : Entails.eval a c8291 := derived8291 a h
  have h4 : Entails.eval a c8290 := derived8290 a h
  have h5 : Entails.eval a c8284 := derived8284 a h
  have h6 : Entails.eval a c8269 := derived8269 a h
  have h7 : Entails.eval a c7994 := derived7994 a h
  have h8 : Entails.eval a c7402 := h 7401 (by decide)
  have h9 : Entails.eval a c6426 := h 6425 (by decide)
  have h10 : Entails.eval a c6492 := h 6491 (by decide)
  have h11 : Entails.eval a c8292 := derived8292 a h
  have h12 : Entails.eval a c8293 := derived8293 a h
  have h13 : Entails.eval a c7325 := h 7324 (by decide)
  have h14 : Entails.eval a c6347 := h 6346 (by decide)
  have h15 : Entails.eval a c6771 := h 6770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8295 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨41, by decide⟩, false), (⟨36, by decide⟩, false), (⟨57, by decide⟩, false), (⟨56, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8295 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c7002, some c6704, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8295 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8295 : lratChecker f8295 p8295 = .success := by decide +kernel
theorem unsat8295 : Unsatisfiable (PosFin 65) f8295 := by
  apply lratCheckerSound f8295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8295
  · intro a ha; simp [p8295] at ha; subst a; trivial
  · exact checked8295
theorem derived8295 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8295 := by
  apply localUnsat_implies_entails f8295 [c8269, c7994, c7002, c6704] c8295 unsat8295 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c7002 := h 7001 (by decide)
  have h3 : Entails.eval a c6704 := h 6703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8296 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8296 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8289, some c8294, some c6583, some c8276, some c6834, some c8291, some c8290, some c8284, some c8269, some c7994, some c8293, some c7309, some c6771, some c7094, some c6911, some c8295, some c7225, some c7338, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8296 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8296 : lratChecker f8296 p8296 = .success := by decide +kernel
theorem unsat8296 : Unsatisfiable (PosFin 65) f8296 := by
  apply lratCheckerSound f8296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8296
  · intro a ha; simp [p8296] at ha; subst a; trivial
  · exact checked8296
theorem derived8296 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8296 := by
  apply localUnsat_implies_entails f8296 [c8289, c8294, c6583, c8276, c6834, c8291, c8290, c8284, c8269, c7994, c8293, c7309, c6771, c7094, c6911, c8295, c7225, c7338] c8296 unsat8296 (by rfl) a
  have h0 : Entails.eval a c8289 := derived8289 a h
  have h1 : Entails.eval a c8294 := derived8294 a h
  have h2 : Entails.eval a c6583 := h 6582 (by decide)
  have h3 : Entails.eval a c8276 := derived8276 a h
  have h4 : Entails.eval a c6834 := h 6833 (by decide)
  have h5 : Entails.eval a c8291 := derived8291 a h
  have h6 : Entails.eval a c8290 := derived8290 a h
  have h7 : Entails.eval a c8284 := derived8284 a h
  have h8 : Entails.eval a c8269 := derived8269 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c8293 := derived8293 a h
  have h11 : Entails.eval a c7309 := h 7308 (by decide)
  have h12 : Entails.eval a c6771 := h 6770 (by decide)
  have h13 : Entails.eval a c7094 := h 7093 (by decide)
  have h14 : Entails.eval a c6911 := h 6910 (by decide)
  have h15 : Entails.eval a c8295 := derived8295 a h
  have h16 : Entails.eval a c7225 := h 7224 (by decide)
  have h17 : Entails.eval a c7338 := h 7337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8297 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨57, by decide⟩, false), (⟨42, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true), (⟨38, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8297 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c7225, some c6846, some c7337, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8297 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8297 : lratChecker f8297 p8297 = .success := by decide +kernel
theorem unsat8297 : Unsatisfiable (PosFin 65) f8297 := by
  apply lratCheckerSound f8297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8297
  · intro a ha; simp [p8297] at ha; subst a; trivial
  · exact checked8297
theorem derived8297 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8297 := by
  apply localUnsat_implies_entails f8297 [c8269, c7994, c7225, c6846, c7337] c8297 unsat8297 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c7225 := h 7224 (by decide)
  have h3 : Entails.eval a c6846 := h 6845 (by decide)
  have h4 : Entails.eval a c7337 := h 7336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8298 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨36, by decide⟩, false), (⟨42, by decide⟩, true), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true), (⟨38, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8298 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c8297, some c7002, some c7511, some c7516, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8298 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8298 : lratChecker f8298 p8298 = .success := by decide +kernel
theorem unsat8298 : Unsatisfiable (PosFin 65) f8298 := by
  apply lratCheckerSound f8298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8298
  · intro a ha; simp [p8298] at ha; subst a; trivial
  · exact checked8298
theorem derived8298 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8298 := by
  apply localUnsat_implies_entails f8298 [c8269, c7994, c8297, c7002, c7511, c7516] c8298 unsat8298 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8297 := derived8297 a h
  have h3 : Entails.eval a c7002 := h 7001 (by decide)
  have h4 : Entails.eval a c7511 := h 7510 (by decide)
  have h5 : Entails.eval a c7516 := h 7515 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8299 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨57, by decide⟩, true), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨33, by decide⟩, true), (⟨43, by decide⟩, false), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8299 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7503, some c7510, some c8224, some c6705, some c7895, some c7519, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8299 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8299 : lratChecker f8299 p8299 = .success := by decide +kernel
theorem unsat8299 : Unsatisfiable (PosFin 65) f8299 := by
  apply lratCheckerSound f8299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8299
  · intro a ha; simp [p8299] at ha; subst a; trivial
  · exact checked8299
theorem derived8299 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8299 := by
  apply localUnsat_implies_entails f8299 [c7503, c7510, c8224, c6705, c7895, c7519] c8299 unsat8299 (by rfl) a
  have h0 : Entails.eval a c7503 := h 7502 (by decide)
  have h1 : Entails.eval a c7510 := h 7509 (by decide)
  have h2 : Entails.eval a c8224 := derived8224 a h
  have h3 : Entails.eval a c6705 := h 6704 (by decide)
  have h4 : Entails.eval a c7895 := derived7895 a h
  have h5 : Entails.eval a c7519 := h 7518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8300 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8300 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c8276, some c8284, some c8289, some c6834, some c8290, some c8291, some c8294, some c6583, some c8296, some c6961, some c7308, some c7093, some c6346, some c6911, some c6426, some c8298, some c8299, some c6947, some c6919, some c7337, some c6845, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8300 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8300 : lratChecker f8300 p8300 = .success := by decide +kernel
theorem unsat8300 : Unsatisfiable (PosFin 65) f8300 := by
  apply lratCheckerSound f8300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8300
  · intro a ha; simp [p8300] at ha; subst a; trivial
  · exact checked8300
theorem derived8300 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8300 := by
  apply localUnsat_implies_entails f8300 [c8269, c7994, c8276, c8284, c8289, c6834, c8290, c8291, c8294, c6583, c8296, c6961, c7308, c7093, c6346, c6911, c6426, c8298, c8299, c6947, c6919, c7337, c6845] c8300 unsat8300 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8276 := derived8276 a h
  have h3 : Entails.eval a c8284 := derived8284 a h
  have h4 : Entails.eval a c8289 := derived8289 a h
  have h5 : Entails.eval a c6834 := h 6833 (by decide)
  have h6 : Entails.eval a c8290 := derived8290 a h
  have h7 : Entails.eval a c8291 := derived8291 a h
  have h8 : Entails.eval a c8294 := derived8294 a h
  have h9 : Entails.eval a c6583 := h 6582 (by decide)
  have h10 : Entails.eval a c8296 := derived8296 a h
  have h11 : Entails.eval a c6961 := h 6960 (by decide)
  have h12 : Entails.eval a c7308 := h 7307 (by decide)
  have h13 : Entails.eval a c7093 := h 7092 (by decide)
  have h14 : Entails.eval a c6346 := h 6345 (by decide)
  have h15 : Entails.eval a c6911 := h 6910 (by decide)
  have h16 : Entails.eval a c6426 := h 6425 (by decide)
  have h17 : Entails.eval a c8298 := derived8298 a h
  have h18 : Entails.eval a c8299 := derived8299 a h
  have h19 : Entails.eval a c6947 := h 6946 (by decide)
  have h20 : Entails.eval a c6919 := h 6918 (by decide)
  have h21 : Entails.eval a c7337 := h 7336 (by decide)
  have h22 : Entails.eval a c6845 := h 6844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8301 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨41, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨34, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8301 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2505, some c3325, some c462, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8301 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8301 : lratChecker f8301 p8301 = .success := by decide +kernel
theorem unsat8301 : Unsatisfiable (PosFin 65) f8301 := by
  apply lratCheckerSound f8301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8301
  · intro a ha; simp [p8301] at ha; subst a; trivial
  · exact checked8301
theorem derived8301 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8301 := by
  apply localUnsat_implies_entails f8301 [c2505, c3325, c462] c8301 unsat8301 (by rfl) a
  have h0 : Entails.eval a c2505 := h 2504 (by decide)
  have h1 : Entails.eval a c3325 := h 3324 (by decide)
  have h2 : Entails.eval a c462 := h 461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8302 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨49, by decide⟩, false), (⟨41, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨34, by decide⟩, false), (⟨56, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8302 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8301, some c871, some c652, some c2017, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8302 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8302 : lratChecker f8302 p8302 = .success := by decide +kernel
theorem unsat8302 : Unsatisfiable (PosFin 65) f8302 := by
  apply lratCheckerSound f8302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8302
  · intro a ha; simp [p8302] at ha; subst a; trivial
  · exact checked8302
theorem derived8302 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8302 := by
  apply localUnsat_implies_entails f8302 [c8301, c871, c652, c2017] c8302 unsat8302 (by rfl) a
  have h0 : Entails.eval a c8301 := derived8301 a h
  have h1 : Entails.eval a c871 := h 870 (by decide)
  have h2 : Entails.eval a c652 := h 651 (by decide)
  have h3 : Entails.eval a c2017 := h 2016 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8303 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨36, by decide⟩, false), (⟨56, by decide⟩, false), (⟨48, by decide⟩, true), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8303 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1637, some c1489, some c1555, some c4814, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8303 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8303 : lratChecker f8303 p8303 = .success := by decide +kernel
theorem unsat8303 : Unsatisfiable (PosFin 65) f8303 := by
  apply lratCheckerSound f8303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8303
  · intro a ha; simp [p8303] at ha; subst a; trivial
  · exact checked8303
theorem derived8303 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8303 := by
  apply localUnsat_implies_entails f8303 [c1637, c1489, c1555, c4814] c8303 unsat8303 (by rfl) a
  have h0 : Entails.eval a c1637 := h 1636 (by decide)
  have h1 : Entails.eval a c1489 := h 1488 (by decide)
  have h2 : Entails.eval a c1555 := h 1554 (by decide)
  have h3 : Entails.eval a c4814 := h 4813 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8304 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨36, by decide⟩, false), (⟨56, by decide⟩, false), (⟨48, by decide⟩, true), (⟨38, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8304 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8303, some c603, some c716, some c2527, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8304 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8304 : lratChecker f8304 p8304 = .success := by decide +kernel
theorem unsat8304 : Unsatisfiable (PosFin 65) f8304 := by
  apply lratCheckerSound f8304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8304
  · intro a ha; simp [p8304] at ha; subst a; trivial
  · exact checked8304
theorem derived8304 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8304 := by
  apply localUnsat_implies_entails f8304 [c8303, c603, c716, c2527] c8304 unsat8304 (by rfl) a
  have h0 : Entails.eval a c8303 := derived8303 a h
  have h1 : Entails.eval a c603 := h 602 (by decide)
  have h2 : Entails.eval a c716 := h 715 (by decide)
  have h3 : Entails.eval a c2527 := h 2526 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8305 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨38, by decide⟩, true), (⟨57, by decide⟩, true), (⟨44, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8305 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c7354, some c7256, some c6961, some c7308, some c6581, some c6848, some c7344, some c7093, some c6346, some c6394, some c6909, some c6895, some c6533, some c7351, some c6841, some c8302, some c8304, some c3958, some c844, some c985, some c3116, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8305 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8305 : lratChecker f8305 p8305 = .success := by decide +kernel
theorem unsat8305 : Unsatisfiable (PosFin 65) f8305 := by
  apply lratCheckerSound f8305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8305
  · intro a ha; simp [p8305] at ha; subst a; trivial
  · exact checked8305
theorem derived8305 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8305 := by
  apply localUnsat_implies_entails f8305 [c8269, c7994, c7354, c7256, c6961, c7308, c6581, c6848, c7344, c7093, c6346, c6394, c6909, c6895, c6533, c7351, c6841, c8302, c8304, c3958, c844, c985, c3116] c8305 unsat8305 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c7354 := h 7353 (by decide)
  have h3 : Entails.eval a c7256 := h 7255 (by decide)
  have h4 : Entails.eval a c6961 := h 6960 (by decide)
  have h5 : Entails.eval a c7308 := h 7307 (by decide)
  have h6 : Entails.eval a c6581 := h 6580 (by decide)
  have h7 : Entails.eval a c6848 := h 6847 (by decide)
  have h8 : Entails.eval a c7344 := h 7343 (by decide)
  have h9 : Entails.eval a c7093 := h 7092 (by decide)
  have h10 : Entails.eval a c6346 := h 6345 (by decide)
  have h11 : Entails.eval a c6394 := h 6393 (by decide)
  have h12 : Entails.eval a c6909 := h 6908 (by decide)
  have h13 : Entails.eval a c6895 := h 6894 (by decide)
  have h14 : Entails.eval a c6533 := h 6532 (by decide)
  have h15 : Entails.eval a c7351 := h 7350 (by decide)
  have h16 : Entails.eval a c6841 := h 6840 (by decide)
  have h17 : Entails.eval a c8302 := derived8302 a h
  have h18 : Entails.eval a c8304 := derived8304 a h
  have h19 : Entails.eval a c3958 := h 3957 (by decide)
  have h20 : Entails.eval a c844 := h 843 (by decide)
  have h21 : Entails.eval a c985 := h 984 (by decide)
  have h22 : Entails.eval a c3116 := h 3115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8306 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨53, by decide⟩, false), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨56, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8306 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c845, some c986, some c970, some c3108, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p8306 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8306 : lratChecker f8306 p8306 = .success := by decide +kernel
theorem unsat8306 : Unsatisfiable (PosFin 65) f8306 := by
  apply lratCheckerSound f8306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8306
  · intro a ha; simp [p8306] at ha; subst a; trivial
  · exact checked8306
theorem derived8306 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8306 := by
  apply localUnsat_implies_entails f8306 [c845, c986, c970, c3108] c8306 unsat8306 (by rfl) a
  have h0 : Entails.eval a c845 := h 844 (by decide)
  have h1 : Entails.eval a c986 := h 985 (by decide)
  have h2 : Entails.eval a c970 := h 969 (by decide)
  have h3 : Entails.eval a c3108 := h 3107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8307 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨39, by decide⟩, false), (⟨56, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8307 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3116, some c2942, some c943, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8307 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8307 : lratChecker f8307 p8307 = .success := by decide +kernel
theorem unsat8307 : Unsatisfiable (PosFin 65) f8307 := by
  apply lratCheckerSound f8307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8307
  · intro a ha; simp [p8307] at ha; subst a; trivial
  · exact checked8307
theorem derived8307 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8307 := by
  apply localUnsat_implies_entails f8307 [c3116, c2942, c943] c8307 unsat8307 (by rfl) a
  have h0 : Entails.eval a c3116 := h 3115 (by decide)
  have h1 : Entails.eval a c2942 := h 2941 (by decide)
  have h2 : Entails.eval a c943 := h 942 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8308 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8308 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1016, some c766, some c2574, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8308 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8308 : lratChecker f8308 p8308 = .success := by decide +kernel
theorem unsat8308 : Unsatisfiable (PosFin 65) f8308 := by
  apply lratCheckerSound f8308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8308
  · intro a ha; simp [p8308] at ha; subst a; trivial
  · exact checked8308
theorem derived8308 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8308 := by
  apply localUnsat_implies_entails f8308 [c1016, c766, c2574] c8308 unsat8308 (by rfl) a
  have h0 : Entails.eval a c1016 := h 1015 (by decide)
  have h1 : Entails.eval a c766 := h 765 (by decide)
  have h2 : Entails.eval a c2574 := h 2573 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8309 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨38, by decide⟩, true), (⟨57, by decide⟩, true), (⟨44, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8309 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8305, some c8300, some c8269, some c7994, some c6961, some c7308, some c7147, some c7215, some c6581, some c6759, some c7008, some c7093, some c6346, some c7018, some c7105, some c7838, some c6906, some c6424, some c7543, some c6895, some c7542, some c7053, some c6695, some c8306, some c8308, some c8307, some c874, some c650, some c1495, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8309 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked8309 : lratChecker f8309 p8309 = .success := by decide +kernel
theorem unsat8309 : Unsatisfiable (PosFin 65) f8309 := by
  apply lratCheckerSound f8309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8309
  · intro a ha; simp [p8309] at ha; subst a; trivial
  · exact checked8309
theorem derived8309 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8309 := by
  apply localUnsat_implies_entails f8309 [c8305, c8300, c8269, c7994, c6961, c7308, c7147, c7215, c6581, c6759, c7008, c7093, c6346, c7018, c7105, c7838, c6906, c6424, c7543, c6895, c7542, c7053, c6695, c8306, c8308, c8307, c874, c650, c1495] c8309 unsat8309 (by rfl) a
  have h0 : Entails.eval a c8305 := derived8305 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c6961 := h 6960 (by decide)
  have h5 : Entails.eval a c7308 := h 7307 (by decide)
  have h6 : Entails.eval a c7147 := h 7146 (by decide)
  have h7 : Entails.eval a c7215 := h 7214 (by decide)
  have h8 : Entails.eval a c6581 := h 6580 (by decide)
  have h9 : Entails.eval a c6759 := h 6758 (by decide)
  have h10 : Entails.eval a c7008 := h 7007 (by decide)
  have h11 : Entails.eval a c7093 := h 7092 (by decide)
  have h12 : Entails.eval a c6346 := h 6345 (by decide)
  have h13 : Entails.eval a c7018 := h 7017 (by decide)
  have h14 : Entails.eval a c7105 := h 7104 (by decide)
  have h15 : Entails.eval a c7838 := derived7838 a h
  have h16 : Entails.eval a c6906 := h 6905 (by decide)
  have h17 : Entails.eval a c6424 := h 6423 (by decide)
  have h18 : Entails.eval a c7543 := h 7542 (by decide)
  have h19 : Entails.eval a c6895 := h 6894 (by decide)
  have h20 : Entails.eval a c7542 := h 7541 (by decide)
  have h21 : Entails.eval a c7053 := h 7052 (by decide)
  have h22 : Entails.eval a c6695 := h 6694 (by decide)
  have h23 : Entails.eval a c8306 := derived8306 a h
  have h24 : Entails.eval a c8308 := derived8308 a h
  have h25 : Entails.eval a c8307 := derived8307 a h
  have h26 : Entails.eval a c874 := h 873 (by decide)
  have h27 : Entails.eval a c650 := h 649 (by decide)
  have h28 : Entails.eval a c1495 := h 1494 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8310 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨63, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8310 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7154, some c8293, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p8310 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8310 : lratChecker f8310 p8310 = .success := by decide +kernel
theorem unsat8310 : Unsatisfiable (PosFin 65) f8310 := by
  apply lratCheckerSound f8310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8310
  · intro a ha; simp [p8310] at ha; subst a; trivial
  · exact checked8310
theorem derived8310 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8310 := by
  apply localUnsat_implies_entails f8310 [c7154, c8293] c8310 unsat8310 (by rfl) a
  have h0 : Entails.eval a c7154 := h 7153 (by decide)
  have h1 : Entails.eval a c8293 := derived8293 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8311 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨44, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8311 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c8310, some c7147, some c7215, some c8309, some c7278, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8311 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8311 : lratChecker f8311 p8311 = .success := by decide +kernel
theorem unsat8311 : Unsatisfiable (PosFin 65) f8311 := by
  apply lratCheckerSound f8311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8311
  · intro a ha; simp [p8311] at ha; subst a; trivial
  · exact checked8311
theorem derived8311 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8311 := by
  apply localUnsat_implies_entails f8311 [c8269, c7994, c8310, c7147, c7215, c8309, c7278] c8311 unsat8311 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8310 := derived8310 a h
  have h3 : Entails.eval a c7147 := h 7146 (by decide)
  have h4 : Entails.eval a c7215 := h 7214 (by decide)
  have h5 : Entails.eval a c8309 := derived8309 a h
  have h6 : Entails.eval a c7278 := h 7277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8312 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨56, by decide⟩, false), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8312 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7437, some c7008, some c7018, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8312 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8312 : lratChecker f8312 p8312 = .success := by decide +kernel
theorem unsat8312 : Unsatisfiable (PosFin 65) f8312 := by
  apply lratCheckerSound f8312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8312
  · intro a ha; simp [p8312] at ha; subst a; trivial
  · exact checked8312
theorem derived8312 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8312 := by
  apply localUnsat_implies_entails f8312 [c7437, c7008, c7018] c8312 unsat8312 (by rfl) a
  have h0 : Entails.eval a c7437 := h 7436 (by decide)
  have h1 : Entails.eval a c7008 := h 7007 (by decide)
  have h2 : Entails.eval a c7018 := h 7017 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8313 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, false), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8313 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8312, some c6530, some c6922, some c6397, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8313 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8313 : lratChecker f8313 p8313 = .success := by decide +kernel
theorem unsat8313 : Unsatisfiable (PosFin 65) f8313 := by
  apply lratCheckerSound f8313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8313
  · intro a ha; simp [p8313] at ha; subst a; trivial
  · exact checked8313
theorem derived8313 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8313 := by
  apply localUnsat_implies_entails f8313 [c8312, c6530, c6922, c6397] c8313 unsat8313 (by rfl) a
  have h0 : Entails.eval a c8312 := derived8312 a h
  have h1 : Entails.eval a c6530 := h 6529 (by decide)
  have h2 : Entails.eval a c6922 := h 6921 (by decide)
  have h3 : Entails.eval a c6397 := h 6396 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8314 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨56, by decide⟩, true), (⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨57, by decide⟩, false), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8314 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6530, some c6954, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8314 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8314 : lratChecker f8314 p8314 = .success := by decide +kernel
theorem unsat8314 : Unsatisfiable (PosFin 65) f8314 := by
  apply lratCheckerSound f8314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8314
  · intro a ha; simp [p8314] at ha; subst a; trivial
  · exact checked8314
theorem derived8314 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8314 := by
  apply localUnsat_implies_entails f8314 [c6530, c6954] c8314 unsat8314 (by rfl) a
  have h0 : Entails.eval a c6530 := h 6529 (by decide)
  have h1 : Entails.eval a c6954 := h 6953 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8315 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8315 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c8269, some c8311, some c7216, some c7148, some c6962, some c6892, some c7027, some c7277, some c7309, some c6347, some c6514, some c8313, some c8314, some c7437, some c7427, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8315 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8315 : lratChecker f8315 p8315 = .success := by decide +kernel
theorem unsat8315 : Unsatisfiable (PosFin 65) f8315 := by
  apply lratCheckerSound f8315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8315
  · intro a ha; simp [p8315] at ha; subst a; trivial
  · exact checked8315
theorem derived8315 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8315 := by
  apply localUnsat_implies_entails f8315 [c8300, c8269, c8311, c7216, c7148, c6962, c6892, c7027, c7277, c7309, c6347, c6514, c8313, c8314, c7437, c7427] c8315 unsat8315 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8311 := derived8311 a h
  have h3 : Entails.eval a c7216 := h 7215 (by decide)
  have h4 : Entails.eval a c7148 := h 7147 (by decide)
  have h5 : Entails.eval a c6962 := h 6961 (by decide)
  have h6 : Entails.eval a c6892 := h 6891 (by decide)
  have h7 : Entails.eval a c7027 := h 7026 (by decide)
  have h8 : Entails.eval a c7277 := h 7276 (by decide)
  have h9 : Entails.eval a c7309 := h 7308 (by decide)
  have h10 : Entails.eval a c6347 := h 6346 (by decide)
  have h11 : Entails.eval a c6514 := h 6513 (by decide)
  have h12 : Entails.eval a c8313 := derived8313 a h
  have h13 : Entails.eval a c8314 := derived8314 a h
  have h14 : Entails.eval a c7437 := h 7436 (by decide)
  have h15 : Entails.eval a c7427 := h 7426 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8316 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨33, by decide⟩, false), (⟨46, by decide⟩, true), (⟨57, by decide⟩, false), (⟨35, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8316 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6771, some c7325, some c6347, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8316 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8316 : lratChecker f8316 p8316 = .success := by decide +kernel
theorem unsat8316 : Unsatisfiable (PosFin 65) f8316 := by
  apply lratCheckerSound f8316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8316
  · intro a ha; simp [p8316] at ha; subst a; trivial
  · exact checked8316
theorem derived8316 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8316 := by
  apply localUnsat_implies_entails f8316 [c8269, c6771, c7325, c6347] c8316 unsat8316 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6771 := h 6770 (by decide)
  have h2 : Entails.eval a c7325 := h 7324 (by decide)
  have h3 : Entails.eval a c6347 := h 6346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8317 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8317 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c6661, some c6680, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8317 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8317 : lratChecker f8317 p8317 = .success := by decide +kernel
theorem unsat8317 : Unsatisfiable (PosFin 65) f8317 := by
  apply lratCheckerSound f8317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8317
  · intro a ha; simp [p8317] at ha; subst a; trivial
  · exact checked8317
theorem derived8317 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8317 := by
  apply localUnsat_implies_entails f8317 [c8300, c6661, c6680] c8317 unsat8317 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c6661 := h 6660 (by decide)
  have h2 : Entails.eval a c6680 := h 6679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8318 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8318 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c8317, some c6587, some c6580, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8318 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8318 : lratChecker f8318 p8318 = .success := by decide +kernel
theorem unsat8318 : Unsatisfiable (PosFin 65) f8318 := by
  apply lratCheckerSound f8318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8318
  · intro a ha; simp [p8318] at ha; subst a; trivial
  · exact checked8318
theorem derived8318 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8318 := by
  apply localUnsat_implies_entails f8318 [c8300, c8317, c6587, c6580] c8318 unsat8318 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c8317 := derived8317 a h
  have h2 : Entails.eval a c6587 := h 6586 (by decide)
  have h3 : Entails.eval a c6580 := h 6579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8319 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8319 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8315, some c8269, some c7216, some c7547, some c6892, some c7492, some c6514, some c8316, some c7277, some c8318, some c6627, some c6288, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8319 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8319 : lratChecker f8319 p8319 = .success := by decide +kernel
theorem unsat8319 : Unsatisfiable (PosFin 65) f8319 := by
  apply lratCheckerSound f8319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8319
  · intro a ha; simp [p8319] at ha; subst a; trivial
  · exact checked8319
theorem derived8319 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8319 := by
  apply localUnsat_implies_entails f8319 [c8315, c8269, c7216, c7547, c6892, c7492, c6514, c8316, c7277, c8318, c6627, c6288] c8319 unsat8319 (by rfl) a
  have h0 : Entails.eval a c8315 := derived8315 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7216 := h 7215 (by decide)
  have h3 : Entails.eval a c7547 := h 7546 (by decide)
  have h4 : Entails.eval a c6892 := h 6891 (by decide)
  have h5 : Entails.eval a c7492 := h 7491 (by decide)
  have h6 : Entails.eval a c6514 := h 6513 (by decide)
  have h7 : Entails.eval a c8316 := derived8316 a h
  have h8 : Entails.eval a c7277 := h 7276 (by decide)
  have h9 : Entails.eval a c8318 := derived8318 a h
  have h10 : Entails.eval a c6627 := h 6626 (by decide)
  have h11 : Entails.eval a c6288 := h 6287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8320 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8320 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8315, some c8269, some c7215, some c6581, some c6741, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8320 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8320 : lratChecker f8320 p8320 = .success := by decide +kernel
theorem unsat8320 : Unsatisfiable (PosFin 65) f8320 := by
  apply lratCheckerSound f8320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8320
  · intro a ha; simp [p8320] at ha; subst a; trivial
  · exact checked8320
theorem derived8320 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8320 := by
  apply localUnsat_implies_entails f8320 [c8315, c8269, c7215, c6581, c6741] c8320 unsat8320 (by rfl) a
  have h0 : Entails.eval a c8315 := derived8315 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7215 := h 7214 (by decide)
  have h3 : Entails.eval a c6581 := h 6580 (by decide)
  have h4 : Entails.eval a c6741 := h 6740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8321 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8321 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6761, some c7221, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p8321 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8321 : lratChecker f8321 p8321 = .success := by decide +kernel
theorem unsat8321 : Unsatisfiable (PosFin 65) f8321 := by
  apply lratCheckerSound f8321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8321
  · intro a ha; simp [p8321] at ha; subst a; trivial
  · exact checked8321
theorem derived8321 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8321 := by
  apply localUnsat_implies_entails f8321 [c6761, c7221] c8321 unsat8321 (by rfl) a
  have h0 : Entails.eval a c6761 := h 6760 (by decide)
  have h1 : Entails.eval a c7221 := h 7220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8322 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8322 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8315, some c8319, some c8320, some c6638, some c6928, some c8321, some c6895, some c6680, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8322 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8322 : lratChecker f8322 p8322 = .success := by decide +kernel
theorem unsat8322 : Unsatisfiable (PosFin 65) f8322 := by
  apply lratCheckerSound f8322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8322
  · intro a ha; simp [p8322] at ha; subst a; trivial
  · exact checked8322
theorem derived8322 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8322 := by
  apply localUnsat_implies_entails f8322 [c7994, c8315, c8319, c8320, c6638, c6928, c8321, c6895, c6680] c8322 unsat8322 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8315 := derived8315 a h
  have h2 : Entails.eval a c8319 := derived8319 a h
  have h3 : Entails.eval a c8320 := derived8320 a h
  have h4 : Entails.eval a c6638 := h 6637 (by decide)
  have h5 : Entails.eval a c6928 := h 6927 (by decide)
  have h6 : Entails.eval a c8321 := derived8321 a h
  have h7 : Entails.eval a c6895 := h 6894 (by decide)
  have h8 : Entails.eval a c6680 := h 6679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8323 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨44, by decide⟩, false), (⟨56, by decide⟩, true), (⟨63, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8323 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7534, some c6509, some c7529, some c6526, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p8323 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8323 : lratChecker f8323 p8323 = .success := by decide +kernel
theorem unsat8323 : Unsatisfiable (PosFin 65) f8323 := by
  apply lratCheckerSound f8323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8323
  · intro a ha; simp [p8323] at ha; subst a; trivial
  · exact checked8323
theorem derived8323 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8323 := by
  apply localUnsat_implies_entails f8323 [c7534, c6509, c7529, c6526] c8323 unsat8323 (by rfl) a
  have h0 : Entails.eval a c7534 := h 7533 (by decide)
  have h1 : Entails.eval a c6509 := h 6508 (by decide)
  have h2 : Entails.eval a c7529 := h 7528 (by decide)
  have h3 : Entails.eval a c6526 := h 6525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8324 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨44, by decide⟩, false), (⟨64, by decide⟩, false), (⟨50, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8324 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7526, some c7531, some c6503, some c6514, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p8324 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8324 : lratChecker f8324 p8324 = .success := by decide +kernel
theorem unsat8324 : Unsatisfiable (PosFin 65) f8324 := by
  apply lratCheckerSound f8324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8324
  · intro a ha; simp [p8324] at ha; subst a; trivial
  · exact checked8324
theorem derived8324 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8324 := by
  apply localUnsat_implies_entails f8324 [c7526, c7531, c6503, c6514] c8324 unsat8324 (by rfl) a
  have h0 : Entails.eval a c7526 := h 7525 (by decide)
  have h1 : Entails.eval a c7531 := h 7530 (by decide)
  have h2 : Entails.eval a c6503 := h 6502 (by decide)
  have h3 : Entails.eval a c6514 := h 6513 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8325 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8325 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c8323, some c8324, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8325 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8325 : lratChecker f8325 p8325 = .success := by decide +kernel
theorem unsat8325 : Unsatisfiable (PosFin 65) f8325 := by
  apply lratCheckerSound f8325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8325
  · intro a ha; simp [p8325] at ha; subst a; trivial
  · exact checked8325
theorem derived8325 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8325 := by
  apply localUnsat_implies_entails f8325 [c8269, c7994, c8323, c8324] c8325 unsat8325 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8323 := derived8323 a h
  have h3 : Entails.eval a c8324 := derived8324 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8326 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨37, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8326 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c8325, some c8310, some c7148, some c6962, some c6997, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8326 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8326 : lratChecker f8326 p8326 = .success := by decide +kernel
theorem unsat8326 : Unsatisfiable (PosFin 65) f8326 := by
  apply lratCheckerSound f8326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8326
  · intro a ha; simp [p8326] at ha; subst a; trivial
  · exact checked8326
theorem derived8326 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8326 := by
  apply localUnsat_implies_entails f8326 [c8269, c7994, c8325, c8310, c7148, c6962, c6997] c8326 unsat8326 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8325 := derived8325 a h
  have h3 : Entails.eval a c8310 := derived8310 a h
  have h4 : Entails.eval a c7148 := h 7147 (by decide)
  have h5 : Entails.eval a c6962 := h 6961 (by decide)
  have h6 : Entails.eval a c6997 := h 6996 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8327 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨42, by decide⟩, false), (⟨37, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8327 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8326, some c8269, some c6961, some c7147, some c6996, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8327 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8327 : lratChecker f8327 p8327 = .success := by decide +kernel
theorem unsat8327 : Unsatisfiable (PosFin 65) f8327 := by
  apply lratCheckerSound f8327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8327
  · intro a ha; simp [p8327] at ha; subst a; trivial
  · exact checked8327
theorem derived8327 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8327 := by
  apply localUnsat_implies_entails f8327 [c8326, c8269, c6961, c7147, c6996] c8327 unsat8327 (by rfl) a
  have h0 : Entails.eval a c8326 := derived8326 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c6961 := h 6960 (by decide)
  have h3 : Entails.eval a c7147 := h 7146 (by decide)
  have h4 : Entails.eval a c6996 := h 6995 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8328 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8328 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8322, some c8326, some c8327, some c6506, some c7532, some c7525, some c6513, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8328 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8328 : lratChecker f8328 p8328 = .success := by decide +kernel
theorem unsat8328 : Unsatisfiable (PosFin 65) f8328 := by
  apply lratCheckerSound f8328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8328
  · intro a ha; simp [p8328] at ha; subst a; trivial
  · exact checked8328
theorem derived8328 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8328 := by
  apply localUnsat_implies_entails f8328 [c8269, c8322, c8326, c8327, c6506, c7532, c7525, c6513] c8328 unsat8328 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8322 := derived8322 a h
  have h2 : Entails.eval a c8326 := derived8326 a h
  have h3 : Entails.eval a c8327 := derived8327 a h
  have h4 : Entails.eval a c6506 := h 6505 (by decide)
  have h5 : Entails.eval a c7532 := h 7531 (by decide)
  have h6 : Entails.eval a c7525 := h 7524 (by decide)
  have h7 : Entails.eval a c6513 := h 6512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8329 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8329 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8325, some c6502, some c7528, some c7532, some c6513, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8329 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8329 : lratChecker f8329 p8329 = .success := by decide +kernel
theorem unsat8329 : Unsatisfiable (PosFin 65) f8329 := by
  apply lratCheckerSound f8329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8329
  · intro a ha; simp [p8329] at ha; subst a; trivial
  · exact checked8329
theorem derived8329 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8329 := by
  apply localUnsat_implies_entails f8329 [c8269, c8325, c6502, c7528, c7532, c6513] c8329 unsat8329 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8325 := derived8325 a h
  have h2 : Entails.eval a c6502 := h 6501 (by decide)
  have h3 : Entails.eval a c7528 := h 7527 (by decide)
  have h4 : Entails.eval a c7532 := h 7531 (by decide)
  have h5 : Entails.eval a c6513 := h 6512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8330 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨56, by decide⟩, false), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8330 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6513, some c6421, some c7137, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8330 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8330 : lratChecker f8330 p8330 = .success := by decide +kernel
theorem unsat8330 : Unsatisfiable (PosFin 65) f8330 := by
  apply lratCheckerSound f8330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8330
  · intro a ha; simp [p8330] at ha; subst a; trivial
  · exact checked8330
theorem derived8330 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8330 := by
  apply localUnsat_implies_entails f8330 [c8269, c6513, c6421, c7137] c8330 unsat8330 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6513 := h 6512 (by decide)
  have h2 : Entails.eval a c6421 := h 6420 (by decide)
  have h3 : Entails.eval a c7137 := h 7136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8331 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨56, by decide⟩, false), (⟨42, by decide⟩, false), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8331 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8329, some c8269, some c7399, some c7202, some c7382, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8331 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8331 : lratChecker f8331 p8331 = .success := by decide +kernel
theorem unsat8331 : Unsatisfiable (PosFin 65) f8331 := by
  apply lratCheckerSound f8331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8331
  · intro a ha; simp [p8331] at ha; subst a; trivial
  · exact checked8331
theorem derived8331 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8331 := by
  apply localUnsat_implies_entails f8331 [c8329, c8269, c7399, c7202, c7382] c8331 unsat8331 (by rfl) a
  have h0 : Entails.eval a c8329 := derived8329 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7399 := h 7398 (by decide)
  have h3 : Entails.eval a c7202 := h 7201 (by decide)
  have h4 : Entails.eval a c7382 := h 7381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8332 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨42, by decide⟩, false), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8332 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8328, some c8269, some c8331, some c8330, some c6488, some c8292, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8332 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8332 : lratChecker f8332 p8332 = .success := by decide +kernel
theorem unsat8332 : Unsatisfiable (PosFin 65) f8332 := by
  apply lratCheckerSound f8332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8332
  · intro a ha; simp [p8332] at ha; subst a; trivial
  · exact checked8332
theorem derived8332 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8332 := by
  apply localUnsat_implies_entails f8332 [c8328, c8269, c8331, c8330, c6488, c8292] c8332 unsat8332 (by rfl) a
  have h0 : Entails.eval a c8328 := derived8328 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8331 := derived8331 a h
  have h3 : Entails.eval a c8330 := derived8330 a h
  have h4 : Entails.eval a c6488 := h 6487 (by decide)
  have h5 : Entails.eval a c8292 := derived8292 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8333 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨41, by decide⟩, true), (⟨56, by decide⟩, true), (⟨44, by decide⟩, true), (⟨59, by decide⟩, true), (⟨52, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8333 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7388, some c7381, some c7380, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8333 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8333 : lratChecker f8333 p8333 = .success := by decide +kernel
theorem unsat8333 : Unsatisfiable (PosFin 65) f8333 := by
  apply lratCheckerSound f8333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8333
  · intro a ha; simp [p8333] at ha; subst a; trivial
  · exact checked8333
theorem derived8333 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8333 := by
  apply localUnsat_implies_entails f8333 [c7388, c7381, c7380] c8333 unsat8333 (by rfl) a
  have h0 : Entails.eval a c7388 := h 7387 (by decide)
  have h1 : Entails.eval a c7381 := h 7380 (by decide)
  have h2 : Entails.eval a c7380 := h 7379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8334 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8334 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6871, some c6903, some c7159, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p8334 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8334 : lratChecker f8334 p8334 = .success := by decide +kernel
theorem unsat8334 : Unsatisfiable (PosFin 65) f8334 := by
  apply lratCheckerSound f8334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8334
  · intro a ha; simp [p8334] at ha; subst a; trivial
  · exact checked8334
theorem derived8334 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8334 := by
  apply localUnsat_implies_entails f8334 [c6871, c6903, c7159] c8334 unsat8334 (by rfl) a
  have h0 : Entails.eval a c6871 := h 6870 (by decide)
  have h1 : Entails.eval a c6903 := h 6902 (by decide)
  have h2 : Entails.eval a c7159 := h 7158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8335 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨39, by decide⟩, false), (⟨41, by decide⟩, true), (⟨56, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8335 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7070, some c6915, some c7143, some c7355, some c7022, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8335 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8335 : lratChecker f8335 p8335 = .success := by decide +kernel
theorem unsat8335 : Unsatisfiable (PosFin 65) f8335 := by
  apply lratCheckerSound f8335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8335
  · intro a ha; simp [p8335] at ha; subst a; trivial
  · exact checked8335
theorem derived8335 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8335 := by
  apply localUnsat_implies_entails f8335 [c7070, c6915, c7143, c7355, c7022] c8335 unsat8335 (by rfl) a
  have h0 : Entails.eval a c7070 := h 7069 (by decide)
  have h1 : Entails.eval a c6915 := h 6914 (by decide)
  have h2 : Entails.eval a c7143 := h 7142 (by decide)
  have h3 : Entails.eval a c7355 := h 7354 (by decide)
  have h4 : Entails.eval a c7022 := h 7021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8336 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨56, by decide⟩, true), (⟨44, by decide⟩, true), (⟨42, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true), (⟨52, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8336 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8333, some c8335, some c8334, some c6994, some c6780, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8336 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8336 : lratChecker f8336 p8336 = .success := by decide +kernel
theorem unsat8336 : Unsatisfiable (PosFin 65) f8336 := by
  apply lratCheckerSound f8336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8336
  · intro a ha; simp [p8336] at ha; subst a; trivial
  · exact checked8336
theorem derived8336 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8336 := by
  apply localUnsat_implies_entails f8336 [c8333, c8335, c8334, c6994, c6780] c8336 unsat8336 (by rfl) a
  have h0 : Entails.eval a c8333 := derived8333 a h
  have h1 : Entails.eval a c8335 := derived8335 a h
  have h2 : Entails.eval a c8334 := derived8334 a h
  have h3 : Entails.eval a c6994 := h 6993 (by decide)
  have h4 : Entails.eval a c6780 := h 6779 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8337 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8337 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c6491, some c6494, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8337 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8337 : lratChecker f8337 p8337 = .success := by decide +kernel
theorem unsat8337 : Unsatisfiable (PosFin 65) f8337 := by
  apply lratCheckerSound f8337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8337
  · intro a ha; simp [p8337] at ha; subst a; trivial
  · exact checked8337
theorem derived8337 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8337 := by
  apply localUnsat_implies_entails f8337 [c8300, c6491, c6494] c8337 unsat8337 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c6491 := h 6490 (by decide)
  have h2 : Entails.eval a c6494 := h 6493 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8338 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8338 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7296, some c7207, some c6427, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p8338 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8338 : lratChecker f8338 p8338 = .success := by decide +kernel
theorem unsat8338 : Unsatisfiable (PosFin 65) f8338 := by
  apply lratCheckerSound f8338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8338
  · intro a ha; simp [p8338] at ha; subst a; trivial
  · exact checked8338
theorem derived8338 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8338 := by
  apply localUnsat_implies_entails f8338 [c7296, c7207, c6427] c8338 unsat8338 (by rfl) a
  have h0 : Entails.eval a c7296 := h 7295 (by decide)
  have h1 : Entails.eval a c7207 := h 7206 (by decide)
  have h2 : Entails.eval a c6427 := h 6426 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8339 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8339 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8328, some c8300, some c7994, some c8329, some c8332, some c8336, some c8337, some c8338, some c7124, some c7312, some c7192, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8339 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8339 : lratChecker f8339 p8339 = .success := by decide +kernel
theorem unsat8339 : Unsatisfiable (PosFin 65) f8339 := by
  apply lratCheckerSound f8339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8339
  · intro a ha; simp [p8339] at ha; subst a; trivial
  · exact checked8339
theorem derived8339 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8339 := by
  apply localUnsat_implies_entails f8339 [c8328, c8300, c7994, c8329, c8332, c8336, c8337, c8338, c7124, c7312, c7192] c8339 unsat8339 (by rfl) a
  have h0 : Entails.eval a c8328 := derived8328 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8329 := derived8329 a h
  have h4 : Entails.eval a c8332 := derived8332 a h
  have h5 : Entails.eval a c8336 := derived8336 a h
  have h6 : Entails.eval a c8337 := derived8337 a h
  have h7 : Entails.eval a c8338 := derived8338 a h
  have h8 : Entails.eval a c7124 := h 7123 (by decide)
  have h9 : Entails.eval a c7312 := h 7311 (by decide)
  have h10 : Entails.eval a c7192 := h 7191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8340 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨44, by decide⟩, true), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8340 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7124, some c7312, some c7192, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8340 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8340 : lratChecker f8340 p8340 = .success := by decide +kernel
theorem unsat8340 : Unsatisfiable (PosFin 65) f8340 := by
  apply lratCheckerSound f8340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8340
  · intro a ha; simp [p8340] at ha; subst a; trivial
  · exact checked8340
theorem derived8340 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8340 := by
  apply localUnsat_implies_entails f8340 [c7124, c7312, c7192] c8340 unsat8340 (by rfl) a
  have h0 : Entails.eval a c7124 := h 7123 (by decide)
  have h1 : Entails.eval a c7312 := h 7311 (by decide)
  have h2 : Entails.eval a c7192 := h 7191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8341 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, true), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8341 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6587, some c6927, some c6711, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p8341 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8341 : lratChecker f8341 p8341 = .success := by decide +kernel
theorem unsat8341 : Unsatisfiable (PosFin 65) f8341 := by
  apply lratCheckerSound f8341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8341
  · intro a ha; simp [p8341] at ha; subst a; trivial
  · exact checked8341
theorem derived8341 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8341 := by
  apply localUnsat_implies_entails f8341 [c6587, c6927, c6711] c8341 unsat8341 (by rfl) a
  have h0 : Entails.eval a c6587 := h 6586 (by decide)
  have h1 : Entails.eval a c6927 := h 6926 (by decide)
  have h2 : Entails.eval a c6711 := h 6710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8342 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8342 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7124, some c7192, some c7201, some c7328, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8342 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8342 : lratChecker f8342 p8342 = .success := by decide +kernel
theorem unsat8342 : Unsatisfiable (PosFin 65) f8342 := by
  apply lratCheckerSound f8342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8342
  · intro a ha; simp [p8342] at ha; subst a; trivial
  · exact checked8342
theorem derived8342 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8342 := by
  apply localUnsat_implies_entails f8342 [c7124, c7192, c7201, c7328] c8342 unsat8342 (by rfl) a
  have h0 : Entails.eval a c7124 := h 7123 (by decide)
  have h1 : Entails.eval a c7192 := h 7191 (by decide)
  have h2 : Entails.eval a c7201 := h 7200 (by decide)
  have h3 : Entails.eval a c7328 := h 7327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8343 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8343 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8339, some c8328, some c8300, some c8269, some c8342, some c8341, some c6581, some c6277, some c7197, some c8330, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8343 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8343 : lratChecker f8343 p8343 = .success := by decide +kernel
theorem unsat8343 : Unsatisfiable (PosFin 65) f8343 := by
  apply lratCheckerSound f8343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8343
  · intro a ha; simp [p8343] at ha; subst a; trivial
  · exact checked8343
theorem derived8343 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8343 := by
  apply localUnsat_implies_entails f8343 [c8339, c8328, c8300, c8269, c8342, c8341, c6581, c6277, c7197, c8330] c8343 unsat8343 (by rfl) a
  have h0 : Entails.eval a c8339 := derived8339 a h
  have h1 : Entails.eval a c8328 := derived8328 a h
  have h2 : Entails.eval a c8300 := derived8300 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c8342 := derived8342 a h
  have h5 : Entails.eval a c8341 := derived8341 a h
  have h6 : Entails.eval a c6581 := h 6580 (by decide)
  have h7 : Entails.eval a c6277 := h 6276 (by decide)
  have h8 : Entails.eval a c7197 := h 7196 (by decide)
  have h9 : Entails.eval a c8330 := derived8330 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8344 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨46, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8344 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8343, some c8339, some c8328, some c8269, some c6581, some c6910, some c6783, some c8330, some c7137, some c7093, some c6288, some c7308, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8344 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8344 : lratChecker f8344 p8344 = .success := by decide +kernel
theorem unsat8344 : Unsatisfiable (PosFin 65) f8344 := by
  apply lratCheckerSound f8344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8344
  · intro a ha; simp [p8344] at ha; subst a; trivial
  · exact checked8344
theorem derived8344 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8344 := by
  apply localUnsat_implies_entails f8344 [c8343, c8339, c8328, c8269, c6581, c6910, c6783, c8330, c7137, c7093, c6288, c7308] c8344 unsat8344 (by rfl) a
  have h0 : Entails.eval a c8343 := derived8343 a h
  have h1 : Entails.eval a c8339 := derived8339 a h
  have h2 : Entails.eval a c8328 := derived8328 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c6581 := h 6580 (by decide)
  have h5 : Entails.eval a c6910 := h 6909 (by decide)
  have h6 : Entails.eval a c6783 := h 6782 (by decide)
  have h7 : Entails.eval a c8330 := derived8330 a h
  have h8 : Entails.eval a c7137 := h 7136 (by decide)
  have h9 : Entails.eval a c7093 := h 7092 (by decide)
  have h10 : Entails.eval a c6288 := h 6287 (by decide)
  have h11 : Entails.eval a c7308 := h 7307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8345 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8345 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8343, some c8339, some c8328, some c8300, some c7994, some c8344, some c6587, some c6927, some c6913, some c6789, some c6762, some c7140, some c6552, some c8316, some c6354, some c7334, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8345 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8345 : lratChecker f8345 p8345 = .success := by decide +kernel
theorem unsat8345 : Unsatisfiable (PosFin 65) f8345 := by
  apply lratCheckerSound f8345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8345
  · intro a ha; simp [p8345] at ha; subst a; trivial
  · exact checked8345
theorem derived8345 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8345 := by
  apply localUnsat_implies_entails f8345 [c8343, c8339, c8328, c8300, c7994, c8344, c6587, c6927, c6913, c6789, c6762, c7140, c6552, c8316, c6354, c7334] c8345 unsat8345 (by rfl) a
  have h0 : Entails.eval a c8343 := derived8343 a h
  have h1 : Entails.eval a c8339 := derived8339 a h
  have h2 : Entails.eval a c8328 := derived8328 a h
  have h3 : Entails.eval a c8300 := derived8300 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c8344 := derived8344 a h
  have h6 : Entails.eval a c6587 := h 6586 (by decide)
  have h7 : Entails.eval a c6927 := h 6926 (by decide)
  have h8 : Entails.eval a c6913 := h 6912 (by decide)
  have h9 : Entails.eval a c6789 := h 6788 (by decide)
  have h10 : Entails.eval a c6762 := h 6761 (by decide)
  have h11 : Entails.eval a c7140 := h 7139 (by decide)
  have h12 : Entails.eval a c6552 := h 6551 (by decide)
  have h13 : Entails.eval a c8316 := derived8316 a h
  have h14 : Entails.eval a c6354 := h 6353 (by decide)
  have h15 : Entails.eval a c7334 := h 7333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8346 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨48, by decide⟩, false), (⟨56, by decide⟩, true), (⟨46, by decide⟩, false), (⟨59, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8346 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c7429, some c7006, some c7017, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8346 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8346 : lratChecker f8346 p8346 = .success := by decide +kernel
theorem unsat8346 : Unsatisfiable (PosFin 65) f8346 := by
  apply lratCheckerSound f8346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8346
  · intro a ha; simp [p8346] at ha; subst a; trivial
  · exact checked8346
theorem derived8346 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8346 := by
  apply localUnsat_implies_entails f8346 [c8269, c7994, c7429, c7006, c7017] c8346 unsat8346 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c7429 := h 7428 (by decide)
  have h3 : Entails.eval a c7006 := h 7005 (by decide)
  have h4 : Entails.eval a c7017 := h 7016 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8347 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨46, by decide⟩, false), (⟨42, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8347 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7177, some c6892, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8347 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8347 : lratChecker f8347 p8347 = .success := by decide +kernel
theorem unsat8347 : Unsatisfiable (PosFin 65) f8347 := by
  apply lratCheckerSound f8347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8347
  · intro a ha; simp [p8347] at ha; subst a; trivial
  · exact checked8347
theorem derived8347 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8347 := by
  apply localUnsat_implies_entails f8347 [c8269, c7177, c6892] c8347 unsat8347 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7177 := h 7176 (by decide)
  have h2 : Entails.eval a c6892 := h 6891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8348 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨41, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8348 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1494, some c3975, some c1296, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p8348 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8348 : lratChecker f8348 p8348 = .success := by decide +kernel
theorem unsat8348 : Unsatisfiable (PosFin 65) f8348 := by
  apply lratCheckerSound f8348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8348
  · intro a ha; simp [p8348] at ha; subst a; trivial
  · exact checked8348
theorem derived8348 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8348 := by
  apply localUnsat_implies_entails f8348 [c1494, c3975, c1296] c8348 unsat8348 (by rfl) a
  have h0 : Entails.eval a c1494 := h 1493 (by decide)
  have h1 : Entails.eval a c3975 := h 3974 (by decide)
  have h2 : Entails.eval a c1296 := h 1295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8349 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨60, by decide⟩, false), (⟨41, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8349 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8348, some c3169, some c3209, some c3538, some c1783, some c4174, some c1386, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8349 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8349 : lratChecker f8349 p8349 = .success := by decide +kernel
theorem unsat8349 : Unsatisfiable (PosFin 65) f8349 := by
  apply lratCheckerSound f8349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8349
  · intro a ha; simp [p8349] at ha; subst a; trivial
  · exact checked8349
theorem derived8349 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8349 := by
  apply localUnsat_implies_entails f8349 [c8348, c3169, c3209, c3538, c1783, c4174, c1386] c8349 unsat8349 (by rfl) a
  have h0 : Entails.eval a c8348 := derived8348 a h
  have h1 : Entails.eval a c3169 := h 3168 (by decide)
  have h2 : Entails.eval a c3209 := h 3208 (by decide)
  have h3 : Entails.eval a c3538 := h 3537 (by decide)
  have h4 : Entails.eval a c1783 := h 1782 (by decide)
  have h5 : Entails.eval a c4174 := h 4173 (by decide)
  have h6 : Entails.eval a c1386 := h 1385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8350 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨60, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8350 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c8349, some c531, some c3036, some c4475, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8350 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8350 : lratChecker f8350 p8350 = .success := by decide +kernel
theorem unsat8350 : Unsatisfiable (PosFin 65) f8350 := by
  apply lratCheckerSound f8350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8350
  · intro a ha; simp [p8350] at ha; subst a; trivial
  · exact checked8350
theorem derived8350 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8350 := by
  apply localUnsat_implies_entails f8350 [c8269, c7994, c8349, c531, c3036, c4475] c8350 unsat8350 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8349 := derived8349 a h
  have h3 : Entails.eval a c531 := h 530 (by decide)
  have h4 : Entails.eval a c3036 := h 3035 (by decide)
  have h5 : Entails.eval a c4475 := h 4474 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8350

end CochromaticTwenty.Certificates.FixedCore0
