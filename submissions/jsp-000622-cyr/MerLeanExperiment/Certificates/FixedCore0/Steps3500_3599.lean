import MerLeanExperiment.Certificates.FixedCore0.Steps3400_3499

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c11051 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11051 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11034, some c11048, some c11049, some c11050, some c10359, some c10541, some c5005, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11051 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11051 : lratChecker f11051 p11051 = .success := by decide +kernel
theorem unsat11051 : Unsatisfiable (PosFin 65) f11051 := by
  apply lratCheckerSound f11051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11051
  · intro a ha; simp [p11051] at ha; subst a; trivial
  · exact checked11051
theorem derived11051 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11051 := by
  apply localUnsat_implies_entails f11051 [c11034, c11048, c11049, c11050, c10359, c10541, c5005] c11051 unsat11051 (by rfl) a
  have h0 : Entails.eval a c11034 := derived11034 a h
  have h1 : Entails.eval a c11048 := derived11048 a h
  have h2 : Entails.eval a c11049 := derived11049 a h
  have h3 : Entails.eval a c11050 := derived11050 a h
  have h4 : Entails.eval a c10359 := derived10359 a h
  have h5 : Entails.eval a c10541 := derived10541 a h
  have h6 : Entails.eval a c5005 := h 5004 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11052 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11052 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4169, some c4171, some c4172, some c10791, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11052 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11052 : lratChecker f11052 p11052 = .success := by decide +kernel
theorem unsat11052 : Unsatisfiable (PosFin 65) f11052 := by
  apply lratCheckerSound f11052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11052
  · intro a ha; simp [p11052] at ha; subst a; trivial
  · exact checked11052
theorem derived11052 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11052 := by
  apply localUnsat_implies_entails f11052 [c4169, c4171, c4172, c10791] c11052 unsat11052 (by rfl) a
  have h0 : Entails.eval a c4169 := h 4168 (by decide)
  have h1 : Entails.eval a c4171 := h 4170 (by decide)
  have h2 : Entails.eval a c4172 := h 4171 (by decide)
  have h3 : Entails.eval a c10791 := derived10791 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11053 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨20, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11053 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10809, some c10507, some c10479, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11053 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11053 : lratChecker f11053 p11053 = .success := by decide +kernel
theorem unsat11053 : Unsatisfiable (PosFin 65) f11053 := by
  apply lratCheckerSound f11053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11053
  · intro a ha; simp [p11053] at ha; subst a; trivial
  · exact checked11053
theorem derived11053 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11053 := by
  apply localUnsat_implies_entails f11053 [c10809, c10507, c10479] c11053 unsat11053 (by rfl) a
  have h0 : Entails.eval a c10809 := derived10809 a h
  have h1 : Entails.eval a c10507 := derived10507 a h
  have h2 : Entails.eval a c10479 := derived10479 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11054 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11054 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10272, some c4193, some c4187, some c10280, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11054 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11054 : lratChecker f11054 p11054 = .success := by decide +kernel
theorem unsat11054 : Unsatisfiable (PosFin 65) f11054 := by
  apply lratCheckerSound f11054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11054
  · intro a ha; simp [p11054] at ha; subst a; trivial
  · exact checked11054
theorem derived11054 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11054 := by
  apply localUnsat_implies_entails f11054 [c11018, c10272, c4193, c4187, c10280] c11054 unsat11054 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10272 := derived10272 a h
  have h2 : Entails.eval a c4193 := h 4192 (by decide)
  have h3 : Entails.eval a c4187 := h 4186 (by decide)
  have h4 : Entails.eval a c10280 := derived10280 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11055 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11055 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11054, some c4179, some c4178, some c10248, some c10277, some c10322, some c4177, some c10245, some c10247, some c10231, some c10261, some c4167, some c4165, some c10783, some c4168, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11055 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11055 : lratChecker f11055 p11055 = .success := by decide +kernel
theorem unsat11055 : Unsatisfiable (PosFin 65) f11055 := by
  apply lratCheckerSound f11055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11055
  · intro a ha; simp [p11055] at ha; subst a; trivial
  · exact checked11055
theorem derived11055 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11055 := by
  apply localUnsat_implies_entails f11055 [c11054, c4179, c4178, c10248, c10277, c10322, c4177, c10245, c10247, c10231, c10261, c4167, c4165, c10783, c4168] c11055 unsat11055 (by rfl) a
  have h0 : Entails.eval a c11054 := derived11054 a h
  have h1 : Entails.eval a c4179 := h 4178 (by decide)
  have h2 : Entails.eval a c4178 := h 4177 (by decide)
  have h3 : Entails.eval a c10248 := derived10248 a h
  have h4 : Entails.eval a c10277 := derived10277 a h
  have h5 : Entails.eval a c10322 := derived10322 a h
  have h6 : Entails.eval a c4177 := h 4176 (by decide)
  have h7 : Entails.eval a c10245 := derived10245 a h
  have h8 : Entails.eval a c10247 := derived10247 a h
  have h9 : Entails.eval a c10231 := derived10231 a h
  have h10 : Entails.eval a c10261 := derived10261 a h
  have h11 : Entails.eval a c4167 := h 4166 (by decide)
  have h12 : Entails.eval a c4165 := h 4164 (by decide)
  have h13 : Entails.eval a c10783 := derived10783 a h
  have h14 : Entails.eval a c4168 := h 4167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11056 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11056 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4179, some c4178, some c10248, some c10247, some c10277, some c10231, some c10322, some c10261, some c4177, some c10245, some c11055, some c11052, some c4166, some c4164, some c10267, some c10264, some c10224, some c4176, some c4175, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p11056 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked11056 : lratChecker f11056 p11056 = .success := by decide +kernel
theorem unsat11056 : Unsatisfiable (PosFin 65) f11056 := by
  apply lratCheckerSound f11056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11056
  · intro a ha; simp [p11056] at ha; subst a; trivial
  · exact checked11056
theorem derived11056 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11056 := by
  apply localUnsat_implies_entails f11056 [c4179, c4178, c10248, c10247, c10277, c10231, c10322, c10261, c4177, c10245, c11055, c11052, c4166, c4164, c10267, c10264, c10224, c4176, c4175] c11056 unsat11056 (by rfl) a
  have h0 : Entails.eval a c4179 := h 4178 (by decide)
  have h1 : Entails.eval a c4178 := h 4177 (by decide)
  have h2 : Entails.eval a c10248 := derived10248 a h
  have h3 : Entails.eval a c10247 := derived10247 a h
  have h4 : Entails.eval a c10277 := derived10277 a h
  have h5 : Entails.eval a c10231 := derived10231 a h
  have h6 : Entails.eval a c10322 := derived10322 a h
  have h7 : Entails.eval a c10261 := derived10261 a h
  have h8 : Entails.eval a c4177 := h 4176 (by decide)
  have h9 : Entails.eval a c10245 := derived10245 a h
  have h10 : Entails.eval a c11055 := derived11055 a h
  have h11 : Entails.eval a c11052 := derived11052 a h
  have h12 : Entails.eval a c4166 := h 4165 (by decide)
  have h13 : Entails.eval a c4164 := h 4163 (by decide)
  have h14 : Entails.eval a c10267 := derived10267 a h
  have h15 : Entails.eval a c10264 := derived10264 a h
  have h16 : Entails.eval a c10224 := derived10224 a h
  have h17 : Entails.eval a c4176 := h 4175 (by decide)
  have h18 : Entails.eval a c4175 := h 4174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11057 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11057 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c4184, some c4185, some c4183, some c4197, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p11057 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11057 : lratChecker f11057 p11057 = .success := by decide +kernel
theorem unsat11057 : Unsatisfiable (PosFin 65) f11057 := by
  apply lratCheckerSound f11057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11057
  · intro a ha; simp [p11057] at ha; subst a; trivial
  · exact checked11057
theorem derived11057 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11057 := by
  apply localUnsat_implies_entails f11057 [c11018, c4184, c4185, c4183, c4197] c11057 unsat11057 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c4184 := h 4183 (by decide)
  have h2 : Entails.eval a c4185 := h 4184 (by decide)
  have h3 : Entails.eval a c4183 := h 4182 (by decide)
  have h4 : Entails.eval a c4197 := h 4196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11058 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨51, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11058 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11056, some c11057, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p11058 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11058 : lratChecker f11058 p11058 = .success := by decide +kernel
theorem unsat11058 : Unsatisfiable (PosFin 65) f11058 := by
  apply lratCheckerSound f11058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11058
  · intro a ha; simp [p11058] at ha; subst a; trivial
  · exact checked11058
theorem derived11058 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11058 := by
  apply localUnsat_implies_entails f11058 [c11056, c11057] c11058 unsat11058 (by rfl) a
  have h0 : Entails.eval a c11056 := derived11056 a h
  have h1 : Entails.eval a c11057 := derived11057 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11059 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11059 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11054, some c11058, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11059 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11059 : lratChecker f11059 p11059 = .success := by decide +kernel
theorem unsat11059 : Unsatisfiable (PosFin 65) f11059 := by
  apply lratCheckerSound f11059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11059
  · intro a ha; simp [p11059] at ha; subst a; trivial
  · exact checked11059
theorem derived11059 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11059 := by
  apply localUnsat_implies_entails f11059 [c11054, c11058] c11059 unsat11059 (by rfl) a
  have h0 : Entails.eval a c11054 := derived11054 a h
  have h1 : Entails.eval a c11058 := derived11058 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11060 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨49, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11060 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11059, some c10277, some c3505, some c3585, some c3978, some c2582, some c2737, some c4548, some c4391, some c2814, some c10717, some c10590, some c3791, some c8380, some c10592, some c10209, some c10288, some c10021, some c10219, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11060 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked11060 : lratChecker f11060 p11060 = .success := by decide +kernel
theorem unsat11060 : Unsatisfiable (PosFin 65) f11060 := by
  apply lratCheckerSound f11060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11060
  · intro a ha; simp [p11060] at ha; subst a; trivial
  · exact checked11060
theorem derived11060 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11060 := by
  apply localUnsat_implies_entails f11060 [c11018, c11059, c10277, c3505, c3585, c3978, c2582, c2737, c4548, c4391, c2814, c10717, c10590, c3791, c8380, c10592, c10209, c10288, c10021, c10219] c11060 unsat11060 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11059 := derived11059 a h
  have h2 : Entails.eval a c10277 := derived10277 a h
  have h3 : Entails.eval a c3505 := h 3504 (by decide)
  have h4 : Entails.eval a c3585 := h 3584 (by decide)
  have h5 : Entails.eval a c3978 := h 3977 (by decide)
  have h6 : Entails.eval a c2582 := h 2581 (by decide)
  have h7 : Entails.eval a c2737 := h 2736 (by decide)
  have h8 : Entails.eval a c4548 := h 4547 (by decide)
  have h9 : Entails.eval a c4391 := h 4390 (by decide)
  have h10 : Entails.eval a c2814 := h 2813 (by decide)
  have h11 : Entails.eval a c10717 := derived10717 a h
  have h12 : Entails.eval a c10590 := derived10590 a h
  have h13 : Entails.eval a c3791 := h 3790 (by decide)
  have h14 : Entails.eval a c8380 := derived8380 a h
  have h15 : Entails.eval a c10592 := derived10592 a h
  have h16 : Entails.eval a c10209 := derived10209 a h
  have h17 : Entails.eval a c10288 := derived10288 a h
  have h18 : Entails.eval a c10021 := derived10021 a h
  have h19 : Entails.eval a c10219 := derived10219 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11061 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11061 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11059, some c11060, some c10251, some c3504, some c10276, some c10279, some c10280, some c10246, some c3789, some c9998, some c2583, some c10278, some c10287, some c10535, some c10299, some c4659, some c10300, some c3978, some c2737, some c10983, some c4390, some c8642, some c242, some c11051, some c3111, some c247, some c8589, some c5913, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11061 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked11061 : lratChecker f11061 p11061 = .success := by decide +kernel
theorem unsat11061 : Unsatisfiable (PosFin 65) f11061 := by
  apply lratCheckerSound f11061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11061
  · intro a ha; simp [p11061] at ha; subst a; trivial
  · exact checked11061
theorem derived11061 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11061 := by
  apply localUnsat_implies_entails f11061 [c11018, c11059, c11060, c10251, c3504, c10276, c10279, c10280, c10246, c3789, c9998, c2583, c10278, c10287, c10535, c10299, c4659, c10300, c3978, c2737, c10983, c4390, c8642, c242, c11051, c3111, c247, c8589, c5913] c11061 unsat11061 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11059 := derived11059 a h
  have h2 : Entails.eval a c11060 := derived11060 a h
  have h3 : Entails.eval a c10251 := derived10251 a h
  have h4 : Entails.eval a c3504 := h 3503 (by decide)
  have h5 : Entails.eval a c10276 := derived10276 a h
  have h6 : Entails.eval a c10279 := derived10279 a h
  have h7 : Entails.eval a c10280 := derived10280 a h
  have h8 : Entails.eval a c10246 := derived10246 a h
  have h9 : Entails.eval a c3789 := h 3788 (by decide)
  have h10 : Entails.eval a c9998 := derived9998 a h
  have h11 : Entails.eval a c2583 := h 2582 (by decide)
  have h12 : Entails.eval a c10278 := derived10278 a h
  have h13 : Entails.eval a c10287 := derived10287 a h
  have h14 : Entails.eval a c10535 := derived10535 a h
  have h15 : Entails.eval a c10299 := derived10299 a h
  have h16 : Entails.eval a c4659 := h 4658 (by decide)
  have h17 : Entails.eval a c10300 := derived10300 a h
  have h18 : Entails.eval a c3978 := h 3977 (by decide)
  have h19 : Entails.eval a c2737 := h 2736 (by decide)
  have h20 : Entails.eval a c10983 := derived10983 a h
  have h21 : Entails.eval a c4390 := h 4389 (by decide)
  have h22 : Entails.eval a c8642 := derived8642 a h
  have h23 : Entails.eval a c242 := h 241 (by decide)
  have h24 : Entails.eval a c11051 := derived11051 a h
  have h25 : Entails.eval a c3111 := h 3110 (by decide)
  have h26 : Entails.eval a c247 := h 246 (by decide)
  have h27 : Entails.eval a c8589 := derived8589 a h
  have h28 : Entails.eval a c5913 := h 5912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11062 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, true), (⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨59, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11062 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c241, some c246, some c10441, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11062 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11062 : lratChecker f11062 p11062 = .success := by decide +kernel
theorem unsat11062 : Unsatisfiable (PosFin 65) f11062 := by
  apply lratCheckerSound f11062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11062
  · intro a ha; simp [p11062] at ha; subst a; trivial
  · exact checked11062
theorem derived11062 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11062 := by
  apply localUnsat_implies_entails f11062 [c241, c246, c10441] c11062 unsat11062 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c10441 := derived10441 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11063 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨55, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11063 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10251, some c10276, some c11059, some c11061, some c3499, some c3577, some c3784, some c10280, some c10279, some c10246, some c10287, some c10278, some c10722, some c10535, some c10299, some c10226, some c4656, some c3976, some c9981, some c11062, some c5571, some c5516, some c10259, some c5745, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11063 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked11063 : lratChecker f11063 p11063 = .success := by decide +kernel
theorem unsat11063 : Unsatisfiable (PosFin 65) f11063 := by
  apply lratCheckerSound f11063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11063
  · intro a ha; simp [p11063] at ha; subst a; trivial
  · exact checked11063
theorem derived11063 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11063 := by
  apply localUnsat_implies_entails f11063 [c11018, c10251, c10276, c11059, c11061, c3499, c3577, c3784, c10280, c10279, c10246, c10287, c10278, c10722, c10535, c10299, c10226, c4656, c3976, c9981, c11062, c5571, c5516, c10259, c5745] c11063 unsat11063 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10251 := derived10251 a h
  have h2 : Entails.eval a c10276 := derived10276 a h
  have h3 : Entails.eval a c11059 := derived11059 a h
  have h4 : Entails.eval a c11061 := derived11061 a h
  have h5 : Entails.eval a c3499 := h 3498 (by decide)
  have h6 : Entails.eval a c3577 := h 3576 (by decide)
  have h7 : Entails.eval a c3784 := h 3783 (by decide)
  have h8 : Entails.eval a c10280 := derived10280 a h
  have h9 : Entails.eval a c10279 := derived10279 a h
  have h10 : Entails.eval a c10246 := derived10246 a h
  have h11 : Entails.eval a c10287 := derived10287 a h
  have h12 : Entails.eval a c10278 := derived10278 a h
  have h13 : Entails.eval a c10722 := derived10722 a h
  have h14 : Entails.eval a c10535 := derived10535 a h
  have h15 : Entails.eval a c10299 := derived10299 a h
  have h16 : Entails.eval a c10226 := derived10226 a h
  have h17 : Entails.eval a c4656 := h 4655 (by decide)
  have h18 : Entails.eval a c3976 := h 3975 (by decide)
  have h19 : Entails.eval a c9981 := derived9981 a h
  have h20 : Entails.eval a c11062 := derived11062 a h
  have h21 : Entails.eval a c5571 := h 5570 (by decide)
  have h22 : Entails.eval a c5516 := h 5515 (by decide)
  have h23 : Entails.eval a c10259 := derived10259 a h
  have h24 : Entails.eval a c5745 := h 5744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11064 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11064 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11061, some c11059, some c10251, some c10276, some c10279, some c10280, some c3499, some c10246, some c3577, some c3784, some c9981, some c10535, some c3976, some c4656, some c10226, some c10299, some c5095, some c2612, some c2809, some c11063, some c10258, some c10606, some c9864, some c11053, some c10637, some c8664, some c10537, some c10600, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11064 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked11064 : lratChecker f11064 p11064 = .success := by decide +kernel
theorem unsat11064 : Unsatisfiable (PosFin 65) f11064 := by
  apply lratCheckerSound f11064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11064
  · intro a ha; simp [p11064] at ha; subst a; trivial
  · exact checked11064
theorem derived11064 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11064 := by
  apply localUnsat_implies_entails f11064 [c11018, c11061, c11059, c10251, c10276, c10279, c10280, c3499, c10246, c3577, c3784, c9981, c10535, c3976, c4656, c10226, c10299, c5095, c2612, c2809, c11063, c10258, c10606, c9864, c11053, c10637, c8664, c10537, c10600] c11064 unsat11064 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11061 := derived11061 a h
  have h2 : Entails.eval a c11059 := derived11059 a h
  have h3 : Entails.eval a c10251 := derived10251 a h
  have h4 : Entails.eval a c10276 := derived10276 a h
  have h5 : Entails.eval a c10279 := derived10279 a h
  have h6 : Entails.eval a c10280 := derived10280 a h
  have h7 : Entails.eval a c3499 := h 3498 (by decide)
  have h8 : Entails.eval a c10246 := derived10246 a h
  have h9 : Entails.eval a c3577 := h 3576 (by decide)
  have h10 : Entails.eval a c3784 := h 3783 (by decide)
  have h11 : Entails.eval a c9981 := derived9981 a h
  have h12 : Entails.eval a c10535 := derived10535 a h
  have h13 : Entails.eval a c3976 := h 3975 (by decide)
  have h14 : Entails.eval a c4656 := h 4655 (by decide)
  have h15 : Entails.eval a c10226 := derived10226 a h
  have h16 : Entails.eval a c10299 := derived10299 a h
  have h17 : Entails.eval a c5095 := h 5094 (by decide)
  have h18 : Entails.eval a c2612 := h 2611 (by decide)
  have h19 : Entails.eval a c2809 := h 2808 (by decide)
  have h20 : Entails.eval a c11063 := derived11063 a h
  have h21 : Entails.eval a c10258 := derived10258 a h
  have h22 : Entails.eval a c10606 := derived10606 a h
  have h23 : Entails.eval a c9864 := derived9864 a h
  have h24 : Entails.eval a c11053 := derived11053 a h
  have h25 : Entails.eval a c10637 := derived10637 a h
  have h26 : Entails.eval a c8664 := derived8664 a h
  have h27 : Entails.eval a c10537 := derived10537 a h
  have h28 : Entails.eval a c10600 := derived10600 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11065 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11065 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11064, some c10254, some c8380, some c11061, some c11059, some c11051, some c3501, some c10781, some c10751, some c4973, some c9759, some c5026, some c4612, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11065 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11065 : lratChecker f11065 p11065 = .success := by decide +kernel
theorem unsat11065 : Unsatisfiable (PosFin 65) f11065 := by
  apply lratCheckerSound f11065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11065
  · intro a ha; simp [p11065] at ha; subst a; trivial
  · exact checked11065
theorem derived11065 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11065 := by
  apply localUnsat_implies_entails f11065 [c11064, c10254, c8380, c11061, c11059, c11051, c3501, c10781, c10751, c4973, c9759, c5026, c4612] c11065 unsat11065 (by rfl) a
  have h0 : Entails.eval a c11064 := derived11064 a h
  have h1 : Entails.eval a c10254 := derived10254 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c11061 := derived11061 a h
  have h4 : Entails.eval a c11059 := derived11059 a h
  have h5 : Entails.eval a c11051 := derived11051 a h
  have h6 : Entails.eval a c3501 := h 3500 (by decide)
  have h7 : Entails.eval a c10781 := derived10781 a h
  have h8 : Entails.eval a c10751 := derived10751 a h
  have h9 : Entails.eval a c4973 := h 4972 (by decide)
  have h10 : Entails.eval a c9759 := derived9759 a h
  have h11 : Entails.eval a c5026 := h 5025 (by decide)
  have h12 : Entails.eval a c4612 := h 4611 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11066 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11066 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11064, some c10277, some c10252, some c10254, some c11065, some c10261, some c10278, some c8380, some c11059, some c10219, some c10021, some c11061, some c3773, some c9810, some c3750, some c3491, some c10273, some c3751, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11066 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked11066 : lratChecker f11066 p11066 = .success := by decide +kernel
theorem unsat11066 : Unsatisfiable (PosFin 65) f11066 := by
  apply lratCheckerSound f11066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11066
  · intro a ha; simp [p11066] at ha; subst a; trivial
  · exact checked11066
theorem derived11066 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11066 := by
  apply localUnsat_implies_entails f11066 [c11018, c11064, c10277, c10252, c10254, c11065, c10261, c10278, c8380, c11059, c10219, c10021, c11061, c3773, c9810, c3750, c3491, c10273, c3751] c11066 unsat11066 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11064 := derived11064 a h
  have h2 : Entails.eval a c10277 := derived10277 a h
  have h3 : Entails.eval a c10252 := derived10252 a h
  have h4 : Entails.eval a c10254 := derived10254 a h
  have h5 : Entails.eval a c11065 := derived11065 a h
  have h6 : Entails.eval a c10261 := derived10261 a h
  have h7 : Entails.eval a c10278 := derived10278 a h
  have h8 : Entails.eval a c8380 := derived8380 a h
  have h9 : Entails.eval a c11059 := derived11059 a h
  have h10 : Entails.eval a c10219 := derived10219 a h
  have h11 : Entails.eval a c10021 := derived10021 a h
  have h12 : Entails.eval a c11061 := derived11061 a h
  have h13 : Entails.eval a c3773 := h 3772 (by decide)
  have h14 : Entails.eval a c9810 := derived9810 a h
  have h15 : Entails.eval a c3750 := h 3749 (by decide)
  have h16 : Entails.eval a c3491 := h 3490 (by decide)
  have h17 : Entails.eval a c10273 := derived10273 a h
  have h18 : Entails.eval a c3751 := h 3750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11067 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11067 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11059, some c3495, some c3494, some c5024, some c10677, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11067 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11067 : lratChecker f11067 p11067 = .success := by decide +kernel
theorem unsat11067 : Unsatisfiable (PosFin 65) f11067 := by
  apply lratCheckerSound f11067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11067
  · intro a ha; simp [p11067] at ha; subst a; trivial
  · exact checked11067
theorem derived11067 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11067 := by
  apply localUnsat_implies_entails f11067 [c11059, c3495, c3494, c5024, c10677] c11067 unsat11067 (by rfl) a
  have h0 : Entails.eval a c11059 := derived11059 a h
  have h1 : Entails.eval a c3495 := h 3494 (by decide)
  have h2 : Entails.eval a c3494 := h 3493 (by decide)
  have h3 : Entails.eval a c5024 := h 5023 (by decide)
  have h4 : Entails.eval a c10677 := derived10677 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11068 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11068 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11064, some c8380, some c11059, some c10277, some c11065, some c10219, some c10021, some c10252, some c11061, some c3490, some c3969, some c10267, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11068 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11068 : lratChecker f11068 p11068 = .success := by decide +kernel
theorem unsat11068 : Unsatisfiable (PosFin 65) f11068 := by
  apply lratCheckerSound f11068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11068
  · intro a ha; simp [p11068] at ha; subst a; trivial
  · exact checked11068
theorem derived11068 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11068 := by
  apply localUnsat_implies_entails f11068 [c11018, c11064, c8380, c11059, c10277, c11065, c10219, c10021, c10252, c11061, c3490, c3969, c10267] c11068 unsat11068 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11064 := derived11064 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c11059 := derived11059 a h
  have h4 : Entails.eval a c10277 := derived10277 a h
  have h5 : Entails.eval a c11065 := derived11065 a h
  have h6 : Entails.eval a c10219 := derived10219 a h
  have h7 : Entails.eval a c10021 := derived10021 a h
  have h8 : Entails.eval a c10252 := derived10252 a h
  have h9 : Entails.eval a c11061 := derived11061 a h
  have h10 : Entails.eval a c3490 := h 3489 (by decide)
  have h11 : Entails.eval a c3969 := h 3968 (by decide)
  have h12 : Entails.eval a c10267 := derived10267 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11069 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11069 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c11059, some c10021, some c3465, some c10274, some c10423, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11069 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11069 : lratChecker f11069 p11069 = .success := by decide +kernel
theorem unsat11069 : Unsatisfiable (PosFin 65) f11069 := by
  apply lratCheckerSound f11069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11069
  · intro a ha; simp [p11069] at ha; subst a; trivial
  · exact checked11069
theorem derived11069 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11069 := by
  apply localUnsat_implies_entails f11069 [c8380, c11059, c10021, c3465, c10274, c10423] c11069 unsat11069 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c11059 := derived11059 a h
  have h2 : Entails.eval a c10021 := derived10021 a h
  have h3 : Entails.eval a c3465 := h 3464 (by decide)
  have h4 : Entails.eval a c10274 := derived10274 a h
  have h5 : Entails.eval a c10423 := derived10423 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11070 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11070 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11066, some c11064, some c8380, some c11059, some c10277, some c11065, some c10219, some c10021, some c11068, some c11069, some c11067, some c3829, some c5021, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11070 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11070 : lratChecker f11070 p11070 = .success := by decide +kernel
theorem unsat11070 : Unsatisfiable (PosFin 65) f11070 := by
  apply lratCheckerSound f11070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11070
  · intro a ha; simp [p11070] at ha; subst a; trivial
  · exact checked11070
theorem derived11070 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11070 := by
  apply localUnsat_implies_entails f11070 [c11066, c11064, c8380, c11059, c10277, c11065, c10219, c10021, c11068, c11069, c11067, c3829, c5021] c11070 unsat11070 (by rfl) a
  have h0 : Entails.eval a c11066 := derived11066 a h
  have h1 : Entails.eval a c11064 := derived11064 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c11059 := derived11059 a h
  have h4 : Entails.eval a c10277 := derived10277 a h
  have h5 : Entails.eval a c11065 := derived11065 a h
  have h6 : Entails.eval a c10219 := derived10219 a h
  have h7 : Entails.eval a c10021 := derived10021 a h
  have h8 : Entails.eval a c11068 := derived11068 a h
  have h9 : Entails.eval a c11069 := derived11069 a h
  have h10 : Entails.eval a c11067 := derived11067 a h
  have h11 : Entails.eval a c3829 := h 3828 (by decide)
  have h12 : Entails.eval a c5021 := h 5020 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11071 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11071 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11064, some c8380, some c11059, some c10277, some c11065, some c10219, some c10021, some c11061, some c11066, some c11070, some c3491, some c10273, some c11067, some c3829, some c5021, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11071 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11071 : lratChecker f11071 p11071 = .success := by decide +kernel
theorem unsat11071 : Unsatisfiable (PosFin 65) f11071 := by
  apply lratCheckerSound f11071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11071
  · intro a ha; simp [p11071] at ha; subst a; trivial
  · exact checked11071
theorem derived11071 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11071 := by
  apply localUnsat_implies_entails f11071 [c11064, c8380, c11059, c10277, c11065, c10219, c10021, c11061, c11066, c11070, c3491, c10273, c11067, c3829, c5021] c11071 unsat11071 (by rfl) a
  have h0 : Entails.eval a c11064 := derived11064 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c11059 := derived11059 a h
  have h3 : Entails.eval a c10277 := derived10277 a h
  have h4 : Entails.eval a c11065 := derived11065 a h
  have h5 : Entails.eval a c10219 := derived10219 a h
  have h6 : Entails.eval a c10021 := derived10021 a h
  have h7 : Entails.eval a c11061 := derived11061 a h
  have h8 : Entails.eval a c11066 := derived11066 a h
  have h9 : Entails.eval a c11070 := derived11070 a h
  have h10 : Entails.eval a c3491 := h 3490 (by decide)
  have h11 : Entails.eval a c10273 := derived10273 a h
  have h12 : Entails.eval a c11067 := derived11067 a h
  have h13 : Entails.eval a c3829 := h 3828 (by decide)
  have h14 : Entails.eval a c5021 := h 5020 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11072 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11072 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3829, some c5092, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p11072 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11072 : lratChecker f11072 p11072 = .success := by decide +kernel
theorem unsat11072 : Unsatisfiable (PosFin 65) f11072 := by
  apply lratCheckerSound f11072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11072
  · intro a ha; simp [p11072] at ha; subst a; trivial
  · exact checked11072
theorem derived11072 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11072 := by
  apply localUnsat_implies_entails f11072 [c3829, c5092] c11072 unsat11072 (by rfl) a
  have h0 : Entails.eval a c3829 := h 3828 (by decide)
  have h1 : Entails.eval a c5092 := h 5091 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11073 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11073 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11064, some c10277, some c11065, some c10219, some c10273, some c10270, some c10274, some c10423, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11073 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11073 : lratChecker f11073 p11073 = .success := by decide +kernel
theorem unsat11073 : Unsatisfiable (PosFin 65) f11073 := by
  apply lratCheckerSound f11073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11073
  · intro a ha; simp [p11073] at ha; subst a; trivial
  · exact checked11073
theorem derived11073 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11073 := by
  apply localUnsat_implies_entails f11073 [c11064, c10277, c11065, c10219, c10273, c10270, c10274, c10423] c11073 unsat11073 (by rfl) a
  have h0 : Entails.eval a c11064 := derived11064 a h
  have h1 : Entails.eval a c10277 := derived10277 a h
  have h2 : Entails.eval a c11065 := derived11065 a h
  have h3 : Entails.eval a c10219 := derived10219 a h
  have h4 : Entails.eval a c10273 := derived10273 a h
  have h5 : Entails.eval a c10270 := derived10270 a h
  have h6 : Entails.eval a c10274 := derived10274 a h
  have h7 : Entails.eval a c10423 := derived10423 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11074 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11074 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11064, some c10277, some c10252, some c11061, some c3490, some c3491, some c10267, some c10512, some c10513, some c10475, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11074 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11074 : lratChecker f11074 p11074 = .success := by decide +kernel
theorem unsat11074 : Unsatisfiable (PosFin 65) f11074 := by
  apply lratCheckerSound f11074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11074
  · intro a ha; simp [p11074] at ha; subst a; trivial
  · exact checked11074
theorem derived11074 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11074 := by
  apply localUnsat_implies_entails f11074 [c11018, c11064, c10277, c10252, c11061, c3490, c3491, c10267, c10512, c10513, c10475] c11074 unsat11074 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11064 := derived11064 a h
  have h2 : Entails.eval a c10277 := derived10277 a h
  have h3 : Entails.eval a c10252 := derived10252 a h
  have h4 : Entails.eval a c11061 := derived11061 a h
  have h5 : Entails.eval a c3490 := h 3489 (by decide)
  have h6 : Entails.eval a c3491 := h 3490 (by decide)
  have h7 : Entails.eval a c10267 := derived10267 a h
  have h8 : Entails.eval a c10512 := derived10512 a h
  have h9 : Entails.eval a c10513 := derived10513 a h
  have h10 : Entails.eval a c10475 := derived10475 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11075 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11075 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11064, some c8380, some c11059, some c10277, some c11065, some c10219, some c10021, some c11071, some c11073, some c11074, some c3495, some c3494, some c11072, some c10677, some c5094, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11075 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11075 : lratChecker f11075 p11075 = .success := by decide +kernel
theorem unsat11075 : Unsatisfiable (PosFin 65) f11075 := by
  apply lratCheckerSound f11075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11075
  · intro a ha; simp [p11075] at ha; subst a; trivial
  · exact checked11075
theorem derived11075 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11075 := by
  apply localUnsat_implies_entails f11075 [c11064, c8380, c11059, c10277, c11065, c10219, c10021, c11071, c11073, c11074, c3495, c3494, c11072, c10677, c5094] c11075 unsat11075 (by rfl) a
  have h0 : Entails.eval a c11064 := derived11064 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c11059 := derived11059 a h
  have h3 : Entails.eval a c10277 := derived10277 a h
  have h4 : Entails.eval a c11065 := derived11065 a h
  have h5 : Entails.eval a c10219 := derived10219 a h
  have h6 : Entails.eval a c10021 := derived10021 a h
  have h7 : Entails.eval a c11071 := derived11071 a h
  have h8 : Entails.eval a c11073 := derived11073 a h
  have h9 : Entails.eval a c11074 := derived11074 a h
  have h10 : Entails.eval a c3495 := h 3494 (by decide)
  have h11 : Entails.eval a c3494 := h 3493 (by decide)
  have h12 : Entails.eval a c11072 := derived11072 a h
  have h13 : Entails.eval a c10677 := derived10677 a h
  have h14 : Entails.eval a c5094 := h 5093 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11076 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11076 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11059, some c3495, some c3494, some c4671, some c10677, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11076 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11076 : lratChecker f11076 p11076 = .success := by decide +kernel
theorem unsat11076 : Unsatisfiable (PosFin 65) f11076 := by
  apply lratCheckerSound f11076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11076
  · intro a ha; simp [p11076] at ha; subst a; trivial
  · exact checked11076
theorem derived11076 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11076 := by
  apply localUnsat_implies_entails f11076 [c11059, c3495, c3494, c4671, c10677] c11076 unsat11076 (by rfl) a
  have h0 : Entails.eval a c11059 := derived11059 a h
  have h1 : Entails.eval a c3495 := h 3494 (by decide)
  have h2 : Entails.eval a c3494 := h 3493 (by decide)
  have h3 : Entails.eval a c4671 := h 4670 (by decide)
  have h4 : Entails.eval a c10677 := derived10677 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11077 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11077 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10267, some c10268, some c10275, some c10475, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11077 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11077 : lratChecker f11077 p11077 = .success := by decide +kernel
theorem unsat11077 : Unsatisfiable (PosFin 65) f11077 := by
  apply lratCheckerSound f11077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11077
  · intro a ha; simp [p11077] at ha; subst a; trivial
  · exact checked11077
theorem derived11077 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11077 := by
  apply localUnsat_implies_entails f11077 [c10267, c10268, c10275, c10475] c11077 unsat11077 (by rfl) a
  have h0 : Entails.eval a c10267 := derived10267 a h
  have h1 : Entails.eval a c10268 := derived10268 a h
  have h2 : Entails.eval a c10275 := derived10275 a h
  have h3 : Entails.eval a c10475 := derived10475 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11078 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨4, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11078 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11064, some c10277, some c10252, some c11061, some c3490, some c3491, some c11077, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11078 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11078 : lratChecker f11078 p11078 = .success := by decide +kernel
theorem unsat11078 : Unsatisfiable (PosFin 65) f11078 := by
  apply lratCheckerSound f11078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11078
  · intro a ha; simp [p11078] at ha; subst a; trivial
  · exact checked11078
theorem derived11078 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11078 := by
  apply localUnsat_implies_entails f11078 [c11018, c11064, c10277, c10252, c11061, c3490, c3491, c11077] c11078 unsat11078 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11064 := derived11064 a h
  have h2 : Entails.eval a c10277 := derived10277 a h
  have h3 : Entails.eval a c10252 := derived10252 a h
  have h4 : Entails.eval a c11061 := derived11061 a h
  have h5 : Entails.eval a c3490 := h 3489 (by decide)
  have h6 : Entails.eval a c3491 := h 3490 (by decide)
  have h7 : Entails.eval a c11077 := derived11077 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11079 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11079 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11061, some c3502, some c11064, some c10277, some c10252, some c3499, some c10245, some c3501, some c3509, some c10273, some c10270, some c10274, some c10266, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11079 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11079 : lratChecker f11079 p11079 = .success := by decide +kernel
theorem unsat11079 : Unsatisfiable (PosFin 65) f11079 := by
  apply lratCheckerSound f11079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11079
  · intro a ha; simp [p11079] at ha; subst a; trivial
  · exact checked11079
theorem derived11079 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11079 := by
  apply localUnsat_implies_entails f11079 [c11018, c11061, c3502, c11064, c10277, c10252, c3499, c10245, c3501, c3509, c10273, c10270, c10274, c10266] c11079 unsat11079 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11061 := derived11061 a h
  have h2 : Entails.eval a c3502 := h 3501 (by decide)
  have h3 : Entails.eval a c11064 := derived11064 a h
  have h4 : Entails.eval a c10277 := derived10277 a h
  have h5 : Entails.eval a c10252 := derived10252 a h
  have h6 : Entails.eval a c3499 := h 3498 (by decide)
  have h7 : Entails.eval a c10245 := derived10245 a h
  have h8 : Entails.eval a c3501 := h 3500 (by decide)
  have h9 : Entails.eval a c3509 := h 3508 (by decide)
  have h10 : Entails.eval a c10273 := derived10273 a h
  have h11 : Entails.eval a c10270 := derived10270 a h
  have h12 : Entails.eval a c10274 := derived10274 a h
  have h13 : Entails.eval a c10266 := derived10266 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11080 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11080 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11059, some c11078, some c11079, some c11076, some c3751, some c3829, some c5021, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11080 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11080 : lratChecker f11080 p11080 = .success := by decide +kernel
theorem unsat11080 : Unsatisfiable (PosFin 65) f11080 := by
  apply lratCheckerSound f11080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11080
  · intro a ha; simp [p11080] at ha; subst a; trivial
  · exact checked11080
theorem derived11080 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11080 := by
  apply localUnsat_implies_entails f11080 [c11059, c11078, c11079, c11076, c3751, c3829, c5021] c11080 unsat11080 (by rfl) a
  have h0 : Entails.eval a c11059 := derived11059 a h
  have h1 : Entails.eval a c11078 := derived11078 a h
  have h2 : Entails.eval a c11079 := derived11079 a h
  have h3 : Entails.eval a c11076 := derived11076 a h
  have h4 : Entails.eval a c3751 := h 3750 (by decide)
  have h5 : Entails.eval a c3829 := h 3828 (by decide)
  have h6 : Entails.eval a c5021 := h 5020 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11081 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11081 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11064, some c10277, some c10252, some c11061, some c11059, some c11080, some c3579, some c3580, some c3577, some c10219, some c10245, some c10021, some c8380, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11081 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11081 : lratChecker f11081 p11081 = .success := by decide +kernel
theorem unsat11081 : Unsatisfiable (PosFin 65) f11081 := by
  apply lratCheckerSound f11081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11081
  · intro a ha; simp [p11081] at ha; subst a; trivial
  · exact checked11081
theorem derived11081 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11081 := by
  apply localUnsat_implies_entails f11081 [c11018, c11064, c10277, c10252, c11061, c11059, c11080, c3579, c3580, c3577, c10219, c10245, c10021, c8380] c11081 unsat11081 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11064 := derived11064 a h
  have h2 : Entails.eval a c10277 := derived10277 a h
  have h3 : Entails.eval a c10252 := derived10252 a h
  have h4 : Entails.eval a c11061 := derived11061 a h
  have h5 : Entails.eval a c11059 := derived11059 a h
  have h6 : Entails.eval a c11080 := derived11080 a h
  have h7 : Entails.eval a c3579 := h 3578 (by decide)
  have h8 : Entails.eval a c3580 := h 3579 (by decide)
  have h9 : Entails.eval a c3577 := h 3576 (by decide)
  have h10 : Entails.eval a c10219 := derived10219 a h
  have h11 : Entails.eval a c10245 := derived10245 a h
  have h12 : Entails.eval a c10021 := derived10021 a h
  have h13 : Entails.eval a c8380 := derived8380 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11082 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11082 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10277, some c10252, some c11081, some c11075, some c9878, some c10657, some c10279, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11082 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11082 : lratChecker f11082 p11082 = .success := by decide +kernel
theorem unsat11082 : Unsatisfiable (PosFin 65) f11082 := by
  apply lratCheckerSound f11082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11082
  · intro a ha; simp [p11082] at ha; subst a; trivial
  · exact checked11082
theorem derived11082 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11082 := by
  apply localUnsat_implies_entails f11082 [c11018, c10277, c10252, c11081, c11075, c9878, c10657, c10279] c11082 unsat11082 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10277 := derived10277 a h
  have h2 : Entails.eval a c10252 := derived10252 a h
  have h3 : Entails.eval a c11081 := derived11081 a h
  have h4 : Entails.eval a c11075 := derived11075 a h
  have h5 : Entails.eval a c9878 := derived9878 a h
  have h6 : Entails.eval a c10657 := derived10657 a h
  have h7 : Entails.eval a c10279 := derived10279 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11083 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11083 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11064, some c11082, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11083 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11083 : lratChecker f11083 p11083 = .success := by decide +kernel
theorem unsat11083 : Unsatisfiable (PosFin 65) f11083 := by
  apply lratCheckerSound f11083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11083
  · intro a ha; simp [p11083] at ha; subst a; trivial
  · exact checked11083
theorem derived11083 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11083 := by
  apply localUnsat_implies_entails f11083 [c11064, c11082] c11083 unsat11083 (by rfl) a
  have h0 : Entails.eval a c11064 := derived11064 a h
  have h1 : Entails.eval a c11082 := derived11082 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11084 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11084 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10272, some c10221, some c10263, some c10280, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11084 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11084 : lratChecker f11084 p11084 = .success := by decide +kernel
theorem unsat11084 : Unsatisfiable (PosFin 65) f11084 := by
  apply lratCheckerSound f11084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11084
  · intro a ha; simp [p11084] at ha; subst a; trivial
  · exact checked11084
theorem derived11084 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11084 := by
  apply localUnsat_implies_entails f11084 [c11018, c10272, c10221, c10263, c10280] c11084 unsat11084 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10272 := derived10272 a h
  have h2 : Entails.eval a c10221 := derived10221 a h
  have h3 : Entails.eval a c10263 := derived10263 a h
  have h4 : Entails.eval a c10280 := derived10280 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11085 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11085 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11083, some c11084, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11085 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11085 : lratChecker f11085 p11085 = .success := by decide +kernel
theorem unsat11085 : Unsatisfiable (PosFin 65) f11085 := by
  apply lratCheckerSound f11085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11085
  · intro a ha; simp [p11085] at ha; subst a; trivial
  · exact checked11085
theorem derived11085 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11085 := by
  apply localUnsat_implies_entails f11085 [c11083, c11084] c11085 unsat11085 (by rfl) a
  have h0 : Entails.eval a c11083 := derived11083 a h
  have h1 : Entails.eval a c11084 := derived11084 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11086 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11086 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4774, some c10601, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p11086 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11086 : lratChecker f11086 p11086 = .success := by decide +kernel
theorem unsat11086 : Unsatisfiable (PosFin 65) f11086 := by
  apply lratCheckerSound f11086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11086
  · intro a ha; simp [p11086] at ha; subst a; trivial
  · exact checked11086
theorem derived11086 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11086 := by
  apply localUnsat_implies_entails f11086 [c4774, c10601] c11086 unsat11086 (by rfl) a
  have h0 : Entails.eval a c4774 := h 4773 (by decide)
  have h1 : Entails.eval a c10601 := derived10601 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11087 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨64, by decide⟩, false), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11087 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11085, some c10831, some c10239, some c3199, some c2950, some c10330, some c4677, some c3614, some c4220, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11087 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11087 : lratChecker f11087 p11087 = .success := by decide +kernel
theorem unsat11087 : Unsatisfiable (PosFin 65) f11087 := by
  apply lratCheckerSound f11087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11087
  · intro a ha; simp [p11087] at ha; subst a; trivial
  · exact checked11087
theorem derived11087 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11087 := by
  apply localUnsat_implies_entails f11087 [c11085, c10831, c10239, c3199, c2950, c10330, c4677, c3614, c4220] c11087 unsat11087 (by rfl) a
  have h0 : Entails.eval a c11085 := derived11085 a h
  have h1 : Entails.eval a c10831 := derived10831 a h
  have h2 : Entails.eval a c10239 := derived10239 a h
  have h3 : Entails.eval a c3199 := h 3198 (by decide)
  have h4 : Entails.eval a c2950 := h 2949 (by decide)
  have h5 : Entails.eval a c10330 := derived10330 a h
  have h6 : Entails.eval a c4677 := h 4676 (by decide)
  have h7 : Entails.eval a c3614 := h 3613 (by decide)
  have h8 : Entails.eval a c4220 := h 4219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11088 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11088 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11085, some c10831, some c10239, some c10370, some c3199, some c10330, some c4677, some c2950, some c4969, some c3645, some c4460, some c11087, some c11086, some c8380, some c10897, some c8300, some c9313, some c10837, some c10283, some c5115, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11088 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked11088 : lratChecker f11088 p11088 = .success := by decide +kernel
theorem unsat11088 : Unsatisfiable (PosFin 65) f11088 := by
  apply lratCheckerSound f11088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11088
  · intro a ha; simp [p11088] at ha; subst a; trivial
  · exact checked11088
theorem derived11088 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11088 := by
  apply localUnsat_implies_entails f11088 [c11018, c11085, c10831, c10239, c10370, c3199, c10330, c4677, c2950, c4969, c3645, c4460, c11087, c11086, c8380, c10897, c8300, c9313, c10837, c10283, c5115] c11088 unsat11088 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c10831 := derived10831 a h
  have h3 : Entails.eval a c10239 := derived10239 a h
  have h4 : Entails.eval a c10370 := derived10370 a h
  have h5 : Entails.eval a c3199 := h 3198 (by decide)
  have h6 : Entails.eval a c10330 := derived10330 a h
  have h7 : Entails.eval a c4677 := h 4676 (by decide)
  have h8 : Entails.eval a c2950 := h 2949 (by decide)
  have h9 : Entails.eval a c4969 := h 4968 (by decide)
  have h10 : Entails.eval a c3645 := h 3644 (by decide)
  have h11 : Entails.eval a c4460 := h 4459 (by decide)
  have h12 : Entails.eval a c11087 := derived11087 a h
  have h13 : Entails.eval a c11086 := derived11086 a h
  have h14 : Entails.eval a c8380 := derived8380 a h
  have h15 : Entails.eval a c10897 := derived10897 a h
  have h16 : Entails.eval a c8300 := derived8300 a h
  have h17 : Entails.eval a c9313 := derived9313 a h
  have h18 : Entails.eval a c10837 := derived10837 a h
  have h19 : Entails.eval a c10283 := derived10283 a h
  have h20 : Entails.eval a c5115 := h 5114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11089 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨59, by decide⟩, false), (⟨9, by decide⟩, false), (⟨62, by decide⟩, false), (⟨54, by decide⟩, true), (⟨11, by decide⟩, false), (⟨14, by decide⟩, false), (⟨64, by decide⟩, true), (⟨57, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11089 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5330, some c1048, some c1047, some c1042, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p11089 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11089 : lratChecker f11089 p11089 = .success := by decide +kernel
theorem unsat11089 : Unsatisfiable (PosFin 65) f11089 := by
  apply lratCheckerSound f11089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11089
  · intro a ha; simp [p11089] at ha; subst a; trivial
  · exact checked11089
theorem derived11089 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11089 := by
  apply localUnsat_implies_entails f11089 [c5330, c1048, c1047, c1042] c11089 unsat11089 (by rfl) a
  have h0 : Entails.eval a c5330 := h 5329 (by decide)
  have h1 : Entails.eval a c1048 := h 1047 (by decide)
  have h2 : Entails.eval a c1047 := h 1046 (by decide)
  have h3 : Entails.eval a c1042 := h 1041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11090 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨53, by decide⟩, true), (⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨4, by decide⟩, false), (⟨7, by decide⟩, false), (⟨64, by decide⟩, true), (⟨57, by decide⟩, false), (⟨51, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11090 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c3193, some c9624, some c4347, some c10320, some c10333, some c4970, some c4464, some c11089, some c288, some c356, some c5849, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p11090 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11090 : lratChecker f11090 p11090 = .success := by decide +kernel
theorem unsat11090 : Unsatisfiable (PosFin 65) f11090 := by
  apply lratCheckerSound f11090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11090
  · intro a ha; simp [p11090] at ha; subst a; trivial
  · exact checked11090
theorem derived11090 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11090 := by
  apply localUnsat_implies_entails f11090 [c11018, c3193, c9624, c4347, c10320, c10333, c4970, c4464, c11089, c288, c356, c5849] c11090 unsat11090 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c3193 := h 3192 (by decide)
  have h2 : Entails.eval a c9624 := derived9624 a h
  have h3 : Entails.eval a c4347 := h 4346 (by decide)
  have h4 : Entails.eval a c10320 := derived10320 a h
  have h5 : Entails.eval a c10333 := derived10333 a h
  have h6 : Entails.eval a c4970 := h 4969 (by decide)
  have h7 : Entails.eval a c4464 := h 4463 (by decide)
  have h8 : Entails.eval a c11089 := derived11089 a h
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c5849 := h 5848 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11091 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨53, by decide⟩, true), (⟨59, by decide⟩, false), (⟨9, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨49, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨64, by decide⟩, true), (⟨57, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11091 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c3822, some c288, some c356, some c2918, some c1044, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p11091 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11091 : lratChecker f11091 p11091 = .success := by decide +kernel
theorem unsat11091 : Unsatisfiable (PosFin 65) f11091 := by
  apply lratCheckerSound f11091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11091
  · intro a ha; simp [p11091] at ha; subst a; trivial
  · exact checked11091
theorem derived11091 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11091 := by
  apply localUnsat_implies_entails f11091 [c11018, c3822, c288, c356, c2918, c1044] c11091 unsat11091 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c3822 := h 3821 (by decide)
  have h2 : Entails.eval a c288 := h 287 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c2918 := h 2917 (by decide)
  have h5 : Entails.eval a c1044 := h 1043 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11092 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨59, by decide⟩, false), (⟨9, by decide⟩, false), (⟨58, by decide⟩, true), (⟨62, by decide⟩, false), (⟨16, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨7, by decide⟩, false), (⟨64, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11092 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5938, some c1044, some c3600, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p11092 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11092 : lratChecker f11092 p11092 = .success := by decide +kernel
theorem unsat11092 : Unsatisfiable (PosFin 65) f11092 := by
  apply lratCheckerSound f11092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11092
  · intro a ha; simp [p11092] at ha; subst a; trivial
  · exact checked11092
theorem derived11092 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11092 := by
  apply localUnsat_implies_entails f11092 [c5938, c1044, c3600] c11092 unsat11092 (by rfl) a
  have h0 : Entails.eval a c5938 := h 5937 (by decide)
  have h1 : Entails.eval a c1044 := h 1043 (by decide)
  have h2 : Entails.eval a c3600 := h 3599 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11093 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨23, by decide⟩, true), (⟨60, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨64, by decide⟩, true), (⟨51, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11093 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c256, some c364, some c5631, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p11093 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11093 : lratChecker f11093 p11093 = .success := by decide +kernel
theorem unsat11093 : Unsatisfiable (PosFin 65) f11093 := by
  apply lratCheckerSound f11093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11093
  · intro a ha; simp [p11093] at ha; subst a; trivial
  · exact checked11093
theorem derived11093 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11093 := by
  apply localUnsat_implies_entails f11093 [c11018, c256, c364, c5631] c11093 unsat11093 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c364 := h 363 (by decide)
  have h3 : Entails.eval a c5631 := h 5630 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11094 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨54, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨64, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11094 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c4347, some c10320, some c10333, some c4970, some c4464, some c3824, some c4997, some c3822, some c5117, some c3676, some c5008, some c3193, some c9624, some c4840, some c5121, some c11091, some c11093, some c11092, some c4797, some c312, some c6145, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p11094 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked11094 : lratChecker f11094 p11094 = .success := by decide +kernel
theorem unsat11094 : Unsatisfiable (PosFin 65) f11094 := by
  apply lratCheckerSound f11094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11094
  · intro a ha; simp [p11094] at ha; subst a; trivial
  · exact checked11094
theorem derived11094 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11094 := by
  apply localUnsat_implies_entails f11094 [c11018, c4347, c10320, c10333, c4970, c4464, c3824, c4997, c3822, c5117, c3676, c5008, c3193, c9624, c4840, c5121, c11091, c11093, c11092, c4797, c312, c6145] c11094 unsat11094 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c4347 := h 4346 (by decide)
  have h2 : Entails.eval a c10320 := derived10320 a h
  have h3 : Entails.eval a c10333 := derived10333 a h
  have h4 : Entails.eval a c4970 := h 4969 (by decide)
  have h5 : Entails.eval a c4464 := h 4463 (by decide)
  have h6 : Entails.eval a c3824 := h 3823 (by decide)
  have h7 : Entails.eval a c4997 := h 4996 (by decide)
  have h8 : Entails.eval a c3822 := h 3821 (by decide)
  have h9 : Entails.eval a c5117 := h 5116 (by decide)
  have h10 : Entails.eval a c3676 := h 3675 (by decide)
  have h11 : Entails.eval a c5008 := h 5007 (by decide)
  have h12 : Entails.eval a c3193 := h 3192 (by decide)
  have h13 : Entails.eval a c9624 := derived9624 a h
  have h14 : Entails.eval a c4840 := h 4839 (by decide)
  have h15 : Entails.eval a c5121 := h 5120 (by decide)
  have h16 : Entails.eval a c11091 := derived11091 a h
  have h17 : Entails.eval a c11093 := derived11093 a h
  have h18 : Entails.eval a c11092 := derived11092 a h
  have h19 : Entails.eval a c4797 := h 4796 (by decide)
  have h20 : Entails.eval a c312 := h 311 (by decide)
  have h21 : Entails.eval a c6145 := h 6144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11095 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨49, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11095 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10552, some c10607, some c312, some c3369, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p11095 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11095 : lratChecker f11095 p11095 = .success := by decide +kernel
theorem unsat11095 : Unsatisfiable (PosFin 65) f11095 := by
  apply lratCheckerSound f11095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11095
  · intro a ha; simp [p11095] at ha; subst a; trivial
  · exact checked11095
theorem derived11095 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11095 := by
  apply localUnsat_implies_entails f11095 [c11018, c10552, c10607, c312, c3369] c11095 unsat11095 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10552 := derived10552 a h
  have h2 : Entails.eval a c10607 := derived10607 a h
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c3369 := h 3368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11096 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨49, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨64, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11096 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c4210, some c4483, some c6050, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11096 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11096 : lratChecker f11096 p11096 = .success := by decide +kernel
theorem unsat11096 : Unsatisfiable (PosFin 65) f11096 := by
  apply lratCheckerSound f11096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11096
  · intro a ha; simp [p11096] at ha; subst a; trivial
  · exact checked11096
theorem derived11096 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11096 := by
  apply localUnsat_implies_entails f11096 [c11018, c4210, c4483, c6050] c11096 unsat11096 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c4210 := h 4209 (by decide)
  have h2 : Entails.eval a c4483 := h 4482 (by decide)
  have h3 : Entails.eval a c6050 := h 6049 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11097 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨52, by decide⟩, false), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11097 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11088, some c11085, some c10389, some c4347, some c10320, some c10333, some c4970, some c3484, some c4464, some c4680, some c2599, some c11094, some c4251, some c4219, some c4491, some c10579, some c10283, some c3193, some c4497, some c10526, some c4490, some c11090, some c11095, some c11096, some c3362, some c11093, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11097 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked11097 : lratChecker f11097 p11097 = .success := by decide +kernel
theorem unsat11097 : Unsatisfiable (PosFin 65) f11097 := by
  apply lratCheckerSound f11097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11097
  · intro a ha; simp [p11097] at ha; subst a; trivial
  · exact checked11097
theorem derived11097 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11097 := by
  apply localUnsat_implies_entails f11097 [c11018, c11088, c11085, c10389, c4347, c10320, c10333, c4970, c3484, c4464, c4680, c2599, c11094, c4251, c4219, c4491, c10579, c10283, c3193, c4497, c10526, c4490, c11090, c11095, c11096, c3362, c11093] c11097 unsat11097 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11088 := derived11088 a h
  have h2 : Entails.eval a c11085 := derived11085 a h
  have h3 : Entails.eval a c10389 := derived10389 a h
  have h4 : Entails.eval a c4347 := h 4346 (by decide)
  have h5 : Entails.eval a c10320 := derived10320 a h
  have h6 : Entails.eval a c10333 := derived10333 a h
  have h7 : Entails.eval a c4970 := h 4969 (by decide)
  have h8 : Entails.eval a c3484 := h 3483 (by decide)
  have h9 : Entails.eval a c4464 := h 4463 (by decide)
  have h10 : Entails.eval a c4680 := h 4679 (by decide)
  have h11 : Entails.eval a c2599 := h 2598 (by decide)
  have h12 : Entails.eval a c11094 := derived11094 a h
  have h13 : Entails.eval a c4251 := h 4250 (by decide)
  have h14 : Entails.eval a c4219 := h 4218 (by decide)
  have h15 : Entails.eval a c4491 := h 4490 (by decide)
  have h16 : Entails.eval a c10579 := derived10579 a h
  have h17 : Entails.eval a c10283 := derived10283 a h
  have h18 : Entails.eval a c3193 := h 3192 (by decide)
  have h19 : Entails.eval a c4497 := h 4496 (by decide)
  have h20 : Entails.eval a c10526 := derived10526 a h
  have h21 : Entails.eval a c4490 := h 4489 (by decide)
  have h22 : Entails.eval a c11090 := derived11090 a h
  have h23 : Entails.eval a c11095 := derived11095 a h
  have h24 : Entails.eval a c11096 := derived11096 a h
  have h25 : Entails.eval a c3362 := h 3361 (by decide)
  have h26 : Entails.eval a c11093 := derived11093 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11098 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, false), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11098 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3614, some c4220, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11098 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11098 : lratChecker f11098 p11098 = .success := by decide +kernel
theorem unsat11098 : Unsatisfiable (PosFin 65) f11098 := by
  apply lratCheckerSound f11098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11098
  · intro a ha; simp [p11098] at ha; subst a; trivial
  · exact checked11098
theorem derived11098 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11098 := by
  apply localUnsat_implies_entails f11098 [c3614, c4220] c11098 unsat11098 (by rfl) a
  have h0 : Entails.eval a c3614 := h 3613 (by decide)
  have h1 : Entails.eval a c4220 := h 4219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11099 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11099 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11085, some c11088, some c10389, some c4347, some c10320, some c10333, some c4680, some c4970, some c4464, some c3484, some c11098, some c5104, some c11086, some c11097, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11099 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11099 : lratChecker f11099 p11099 = .success := by decide +kernel
theorem unsat11099 : Unsatisfiable (PosFin 65) f11099 := by
  apply lratCheckerSound f11099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11099
  · intro a ha; simp [p11099] at ha; subst a; trivial
  · exact checked11099
theorem derived11099 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11099 := by
  apply localUnsat_implies_entails f11099 [c11018, c11085, c11088, c10389, c4347, c10320, c10333, c4680, c4970, c4464, c3484, c11098, c5104, c11086, c11097] c11099 unsat11099 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c11088 := derived11088 a h
  have h3 : Entails.eval a c10389 := derived10389 a h
  have h4 : Entails.eval a c4347 := h 4346 (by decide)
  have h5 : Entails.eval a c10320 := derived10320 a h
  have h6 : Entails.eval a c10333 := derived10333 a h
  have h7 : Entails.eval a c4680 := h 4679 (by decide)
  have h8 : Entails.eval a c4970 := h 4969 (by decide)
  have h9 : Entails.eval a c4464 := h 4463 (by decide)
  have h10 : Entails.eval a c3484 := h 3483 (by decide)
  have h11 : Entails.eval a c11098 := derived11098 a h
  have h12 : Entails.eval a c5104 := h 5103 (by decide)
  have h13 : Entails.eval a c11086 := derived11086 a h
  have h14 : Entails.eval a c11097 := derived11097 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11100 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11100 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11085, some c10573, some c10253, some c4831, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11100 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11100 : lratChecker f11100 p11100 = .success := by decide +kernel
theorem unsat11100 : Unsatisfiable (PosFin 65) f11100 := by
  apply lratCheckerSound f11100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11100
  · intro a ha; simp [p11100] at ha; subst a; trivial
  · exact checked11100
theorem derived11100 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11100 := by
  apply localUnsat_implies_entails f11100 [c11018, c11085, c10573, c10253, c4831] c11100 unsat11100 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c10573 := derived10573 a h
  have h3 : Entails.eval a c10253 := derived10253 a h
  have h4 : Entails.eval a c4831 := h 4830 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11101 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11101 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11085, some c11100, some c11099, some c10256, some c4823, some c10588, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11101 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11101 : lratChecker f11101 p11101 = .success := by decide +kernel
theorem unsat11101 : Unsatisfiable (PosFin 65) f11101 := by
  apply lratCheckerSound f11101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11101
  · intro a ha; simp [p11101] at ha; subst a; trivial
  · exact checked11101
theorem derived11101 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11101 := by
  apply localUnsat_implies_entails f11101 [c11018, c11085, c11100, c11099, c10256, c4823, c10588] c11101 unsat11101 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c11100 := derived11100 a h
  have h3 : Entails.eval a c11099 := derived11099 a h
  have h4 : Entails.eval a c10256 := derived10256 a h
  have h5 : Entails.eval a c4823 := h 4822 (by decide)
  have h6 : Entails.eval a c10588 := derived10588 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11102 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨50, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11102 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11101, some c10397, some c10534, some c10395, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11102 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11102 : lratChecker f11102 p11102 = .success := by decide +kernel
theorem unsat11102 : Unsatisfiable (PosFin 65) f11102 := by
  apply lratCheckerSound f11102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11102
  · intro a ha; simp [p11102] at ha; subst a; trivial
  · exact checked11102
theorem derived11102 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11102 := by
  apply localUnsat_implies_entails f11102 [c11018, c11101, c10397, c10534, c10395] c11102 unsat11102 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c10397 := derived10397 a h
  have h3 : Entails.eval a c10534 := derived10534 a h
  have h4 : Entails.eval a c10395 := derived10395 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11103 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11103 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11102, some c11101, some c11085, some c4829, some c4830, some c4843, some c4826, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11103 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11103 : lratChecker f11103 p11103 = .success := by decide +kernel
theorem unsat11103 : Unsatisfiable (PosFin 65) f11103 := by
  apply lratCheckerSound f11103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11103
  · intro a ha; simp [p11103] at ha; subst a; trivial
  · exact checked11103
theorem derived11103 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11103 := by
  apply localUnsat_implies_entails f11103 [c11018, c11102, c11101, c11085, c4829, c4830, c4843, c4826] c11103 unsat11103 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11102 := derived11102 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c11085 := derived11085 a h
  have h4 : Entails.eval a c4829 := h 4828 (by decide)
  have h5 : Entails.eval a c4830 := h 4829 (by decide)
  have h6 : Entails.eval a c4843 := h 4842 (by decide)
  have h7 : Entails.eval a c4826 := h 4825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11104 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11104 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11102, some c8269, some c11101, some c11085, some c11103, some c10392, some c10535, some c10536, some c10237, some c11051, some c10222, some c10719, some c10298, some c5002, some c5103, some c2789, some c2890, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11104 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11104 : lratChecker f11104 p11104 = .success := by decide +kernel
theorem unsat11104 : Unsatisfiable (PosFin 65) f11104 := by
  apply lratCheckerSound f11104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11104
  · intro a ha; simp [p11104] at ha; subst a; trivial
  · exact checked11104
theorem derived11104 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11104 := by
  apply localUnsat_implies_entails f11104 [c11018, c11102, c8269, c11101, c11085, c11103, c10392, c10535, c10536, c10237, c11051, c10222, c10719, c10298, c5002, c5103, c2789, c2890] c11104 unsat11104 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11102 := derived11102 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c11101 := derived11101 a h
  have h4 : Entails.eval a c11085 := derived11085 a h
  have h5 : Entails.eval a c11103 := derived11103 a h
  have h6 : Entails.eval a c10392 := derived10392 a h
  have h7 : Entails.eval a c10535 := derived10535 a h
  have h8 : Entails.eval a c10536 := derived10536 a h
  have h9 : Entails.eval a c10237 := derived10237 a h
  have h10 : Entails.eval a c11051 := derived11051 a h
  have h11 : Entails.eval a c10222 := derived10222 a h
  have h12 : Entails.eval a c10719 := derived10719 a h
  have h13 : Entails.eval a c10298 := derived10298 a h
  have h14 : Entails.eval a c5002 := h 5001 (by decide)
  have h15 : Entails.eval a c5103 := h 5102 (by decide)
  have h16 : Entails.eval a c2789 := h 2788 (by decide)
  have h17 : Entails.eval a c2890 := h 2889 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11105 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨60, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨62, by decide⟩, false), (⟨16, by decide⟩, false), (⟨50, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11105 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c10719, some c10298, some c10161, some c4526, some c5109, some c3543, some c2958, some c2692, some c5001, some c5002, some c3440, some c9185, some c9143, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p11105 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11105 : lratChecker f11105 p11105 = .success := by decide +kernel
theorem unsat11105 : Unsatisfiable (PosFin 65) f11105 := by
  apply lratCheckerSound f11105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11105
  · intro a ha; simp [p11105] at ha; subst a; trivial
  · exact checked11105
theorem derived11105 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11105 := by
  apply localUnsat_implies_entails f11105 [c8269, c10719, c10298, c10161, c4526, c5109, c3543, c2958, c2692, c5001, c5002, c3440, c9185, c9143] c11105 unsat11105 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c10719 := derived10719 a h
  have h2 : Entails.eval a c10298 := derived10298 a h
  have h3 : Entails.eval a c10161 := derived10161 a h
  have h4 : Entails.eval a c4526 := h 4525 (by decide)
  have h5 : Entails.eval a c5109 := h 5108 (by decide)
  have h6 : Entails.eval a c3543 := h 3542 (by decide)
  have h7 : Entails.eval a c2958 := h 2957 (by decide)
  have h8 : Entails.eval a c2692 := h 2691 (by decide)
  have h9 : Entails.eval a c5001 := h 5000 (by decide)
  have h10 : Entails.eval a c5002 := h 5001 (by decide)
  have h11 : Entails.eval a c3440 := h 3439 (by decide)
  have h12 : Entails.eval a c9185 := derived9185 a h
  have h13 : Entails.eval a c9143 := derived9143 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11106 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11106 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11104, some c11102, some c11101, some c11085, some c9878, some c10535, some c11105, some c2923, some c5118, some c2681, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11106 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11106 : lratChecker f11106 p11106 = .success := by decide +kernel
theorem unsat11106 : Unsatisfiable (PosFin 65) f11106 := by
  apply lratCheckerSound f11106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11106
  · intro a ha; simp [p11106] at ha; subst a; trivial
  · exact checked11106
theorem derived11106 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11106 := by
  apply localUnsat_implies_entails f11106 [c11104, c11102, c11101, c11085, c9878, c10535, c11105, c2923, c5118, c2681] c11106 unsat11106 (by rfl) a
  have h0 : Entails.eval a c11104 := derived11104 a h
  have h1 : Entails.eval a c11102 := derived11102 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c11085 := derived11085 a h
  have h4 : Entails.eval a c9878 := derived9878 a h
  have h5 : Entails.eval a c10535 := derived10535 a h
  have h6 : Entails.eval a c11105 := derived11105 a h
  have h7 : Entails.eval a c2923 := h 2922 (by decide)
  have h8 : Entails.eval a c5118 := h 5117 (by decide)
  have h9 : Entails.eval a c2681 := h 2680 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11107 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11107 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11104, some c11102, some c8269, some c11101, some c11085, some c11106, some c4832, some c4830, some c4835, some c4353, some c4826, some c10351, some c10921, some c5008, some c5001, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11107 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11107 : lratChecker f11107 p11107 = .success := by decide +kernel
theorem unsat11107 : Unsatisfiable (PosFin 65) f11107 := by
  apply lratCheckerSound f11107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11107
  · intro a ha; simp [p11107] at ha; subst a; trivial
  · exact checked11107
theorem derived11107 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11107 := by
  apply localUnsat_implies_entails f11107 [c11104, c11102, c8269, c11101, c11085, c11106, c4832, c4830, c4835, c4353, c4826, c10351, c10921, c5008, c5001] c11107 unsat11107 (by rfl) a
  have h0 : Entails.eval a c11104 := derived11104 a h
  have h1 : Entails.eval a c11102 := derived11102 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c11101 := derived11101 a h
  have h4 : Entails.eval a c11085 := derived11085 a h
  have h5 : Entails.eval a c11106 := derived11106 a h
  have h6 : Entails.eval a c4832 := h 4831 (by decide)
  have h7 : Entails.eval a c4830 := h 4829 (by decide)
  have h8 : Entails.eval a c4835 := h 4834 (by decide)
  have h9 : Entails.eval a c4353 := h 4352 (by decide)
  have h10 : Entails.eval a c4826 := h 4825 (by decide)
  have h11 : Entails.eval a c10351 := derived10351 a h
  have h12 : Entails.eval a c10921 := derived10921 a h
  have h13 : Entails.eval a c5008 := h 5007 (by decide)
  have h14 : Entails.eval a c5001 := h 5000 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11108 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11108 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11085, some c11102, some c11107, some c10392, some c4829, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11108 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11108 : lratChecker f11108 p11108 = .success := by decide +kernel
theorem unsat11108 : Unsatisfiable (PosFin 65) f11108 := by
  apply lratCheckerSound f11108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11108
  · intro a ha; simp [p11108] at ha; subst a; trivial
  · exact checked11108
theorem derived11108 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11108 := by
  apply localUnsat_implies_entails f11108 [c11018, c11085, c11102, c11107, c10392, c4829] c11108 unsat11108 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c11102 := derived11102 a h
  have h3 : Entails.eval a c11107 := derived11107 a h
  have h4 : Entails.eval a c10392 := derived10392 a h
  have h5 : Entails.eval a c4829 := h 4828 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11109 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨58, by decide⟩, true), (⟨54, by decide⟩, false), (⟨60, by decide⟩, true), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11109 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11085, some c4353, some c3208, some c10353, some c10921, some c2958, some c3681, some c10923, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11109 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11109 : lratChecker f11109 p11109 = .success := by decide +kernel
theorem unsat11109 : Unsatisfiable (PosFin 65) f11109 := by
  apply lratCheckerSound f11109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11109
  · intro a ha; simp [p11109] at ha; subst a; trivial
  · exact checked11109
theorem derived11109 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11109 := by
  apply localUnsat_implies_entails f11109 [c11108, c11085, c4353, c3208, c10353, c10921, c2958, c3681, c10923] c11109 unsat11109 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c4353 := h 4352 (by decide)
  have h3 : Entails.eval a c3208 := h 3207 (by decide)
  have h4 : Entails.eval a c10353 := derived10353 a h
  have h5 : Entails.eval a c10921 := derived10921 a h
  have h6 : Entails.eval a c2958 := h 2957 (by decide)
  have h7 : Entails.eval a c3681 := h 3680 (by decide)
  have h8 : Entails.eval a c10923 := derived10923 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11110 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨56, by decide⟩, false), (⟨58, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨60, by decide⟩, true), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11110 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11085, some c11109, some c7994, some c3203, some c4338, some c3618, some c2955, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11110 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11110 : lratChecker f11110 p11110 = .success := by decide +kernel
theorem unsat11110 : Unsatisfiable (PosFin 65) f11110 := by
  apply lratCheckerSound f11110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11110
  · intro a ha; simp [p11110] at ha; subst a; trivial
  · exact checked11110
theorem derived11110 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11110 := by
  apply localUnsat_implies_entails f11110 [c11108, c11085, c11109, c7994, c3203, c4338, c3618, c2955] c11110 unsat11110 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c11109 := derived11109 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c3203 := h 3202 (by decide)
  have h5 : Entails.eval a c4338 := h 4337 (by decide)
  have h6 : Entails.eval a c3618 := h 3617 (by decide)
  have h7 : Entails.eval a c2955 := h 2954 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11111 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨59, by decide⟩, true), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11111 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11108, some c11085, some c3203, some c8380, some c4338, some c3120, some c10340, some c10896, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11111 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11111 : lratChecker f11111 p11111 = .success := by decide +kernel
theorem unsat11111 : Unsatisfiable (PosFin 65) f11111 := by
  apply lratCheckerSound f11111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11111
  · intro a ha; simp [p11111] at ha; subst a; trivial
  · exact checked11111
theorem derived11111 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11111 := by
  apply localUnsat_implies_entails f11111 [c11018, c11108, c11085, c3203, c8380, c4338, c3120, c10340, c10896] c11111 unsat11111 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11085 := derived11085 a h
  have h3 : Entails.eval a c3203 := h 3202 (by decide)
  have h4 : Entails.eval a c8380 := derived8380 a h
  have h5 : Entails.eval a c4338 := h 4337 (by decide)
  have h6 : Entails.eval a c3120 := h 3119 (by decide)
  have h7 : Entails.eval a c10340 := derived10340 a h
  have h8 : Entails.eval a c10896 := derived10896 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11112 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨14, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11112 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11085, some c11101, some c4820, some c11108, some c4818, some c4819, some c4835, some c4821, some c4842, some c4795, some c4792, some c4794, some c4751, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11112 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11112 : lratChecker f11112 p11112 = .success := by decide +kernel
theorem unsat11112 : Unsatisfiable (PosFin 65) f11112 := by
  apply lratCheckerSound f11112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11112
  · intro a ha; simp [p11112] at ha; subst a; trivial
  · exact checked11112
theorem derived11112 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11112 := by
  apply localUnsat_implies_entails f11112 [c11085, c11101, c4820, c11108, c4818, c4819, c4835, c4821, c4842, c4795, c4792, c4794, c4751] c11112 unsat11112 (by rfl) a
  have h0 : Entails.eval a c11085 := derived11085 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c4820 := h 4819 (by decide)
  have h3 : Entails.eval a c11108 := derived11108 a h
  have h4 : Entails.eval a c4818 := h 4817 (by decide)
  have h5 : Entails.eval a c4819 := h 4818 (by decide)
  have h6 : Entails.eval a c4835 := h 4834 (by decide)
  have h7 : Entails.eval a c4821 := h 4820 (by decide)
  have h8 : Entails.eval a c4842 := h 4841 (by decide)
  have h9 : Entails.eval a c4795 := h 4794 (by decide)
  have h10 : Entails.eval a c4792 := h 4791 (by decide)
  have h11 : Entails.eval a c4794 := h 4793 (by decide)
  have h12 : Entails.eval a c4751 := h 4750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11113 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11113 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11101, some c11085, some c4754, some c4756, some c4796, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11113 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11113 : lratChecker f11113 p11113 = .success := by decide +kernel
theorem unsat11113 : Unsatisfiable (PosFin 65) f11113 := by
  apply lratCheckerSound f11113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11113
  · intro a ha; simp [p11113] at ha; subst a; trivial
  · exact checked11113
theorem derived11113 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11113 := by
  apply localUnsat_implies_entails f11113 [c11101, c11085, c4754, c4756, c4796] c11113 unsat11113 (by rfl) a
  have h0 : Entails.eval a c11101 := derived11101 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c4754 := h 4753 (by decide)
  have h3 : Entails.eval a c4756 := h 4755 (by decide)
  have h4 : Entails.eval a c4796 := h 4795 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11114 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11114 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11085, some c4819, some c4818, some c4835, some c4821, some c11101, some c4820, some c4842, some c11110, some c11112, some c11113, some c4793, some c4797, some c4790, some c4799, some c4752, some c4743, some c4771, some c4815, some c4802, some c4789, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11114 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked11114 : lratChecker f11114 p11114 = .success := by decide +kernel
theorem unsat11114 : Unsatisfiable (PosFin 65) f11114 := by
  apply lratCheckerSound f11114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11114
  · intro a ha; simp [p11114] at ha; subst a; trivial
  · exact checked11114
theorem derived11114 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11114 := by
  apply localUnsat_implies_entails f11114 [c11108, c11085, c4819, c4818, c4835, c4821, c11101, c4820, c4842, c11110, c11112, c11113, c4793, c4797, c4790, c4799, c4752, c4743, c4771, c4815, c4802, c4789] c11114 unsat11114 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c4819 := h 4818 (by decide)
  have h3 : Entails.eval a c4818 := h 4817 (by decide)
  have h4 : Entails.eval a c4835 := h 4834 (by decide)
  have h5 : Entails.eval a c4821 := h 4820 (by decide)
  have h6 : Entails.eval a c11101 := derived11101 a h
  have h7 : Entails.eval a c4820 := h 4819 (by decide)
  have h8 : Entails.eval a c4842 := h 4841 (by decide)
  have h9 : Entails.eval a c11110 := derived11110 a h
  have h10 : Entails.eval a c11112 := derived11112 a h
  have h11 : Entails.eval a c11113 := derived11113 a h
  have h12 : Entails.eval a c4793 := h 4792 (by decide)
  have h13 : Entails.eval a c4797 := h 4796 (by decide)
  have h14 : Entails.eval a c4790 := h 4789 (by decide)
  have h15 : Entails.eval a c4799 := h 4798 (by decide)
  have h16 : Entails.eval a c4752 := h 4751 (by decide)
  have h17 : Entails.eval a c4743 := h 4742 (by decide)
  have h18 : Entails.eval a c4771 := h 4770 (by decide)
  have h19 : Entails.eval a c4815 := h 4814 (by decide)
  have h20 : Entails.eval a c4802 := h 4801 (by decide)
  have h21 : Entails.eval a c4789 := h 4788 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11115 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11115 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4793, some c4797, some c10378, some c4474, some c5111, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p11115 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11115 : lratChecker f11115 p11115 = .success := by decide +kernel
theorem unsat11115 : Unsatisfiable (PosFin 65) f11115 := by
  apply lratCheckerSound f11115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11115
  · intro a ha; simp [p11115] at ha; subst a; trivial
  · exact checked11115
theorem derived11115 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11115 := by
  apply localUnsat_implies_entails f11115 [c4793, c4797, c10378, c4474, c5111] c11115 unsat11115 (by rfl) a
  have h0 : Entails.eval a c4793 := h 4792 (by decide)
  have h1 : Entails.eval a c4797 := h 4796 (by decide)
  have h2 : Entails.eval a c10378 := derived10378 a h
  have h3 : Entails.eval a c4474 := h 4473 (by decide)
  have h4 : Entails.eval a c5111 := h 5110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11116 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨20, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11116 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11085, some c4794, some c4798, some c10453, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11116 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11116 : lratChecker f11116 p11116 = .success := by decide +kernel
theorem unsat11116 : Unsatisfiable (PosFin 65) f11116 := by
  apply lratCheckerSound f11116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11116
  · intro a ha; simp [p11116] at ha; subst a; trivial
  · exact checked11116
theorem derived11116 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11116 := by
  apply localUnsat_implies_entails f11116 [c11108, c11085, c4794, c4798, c10453] c11116 unsat11116 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c4794 := h 4793 (by decide)
  have h3 : Entails.eval a c4798 := h 4797 (by decide)
  have h4 : Entails.eval a c10453 := derived10453 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11117 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11117 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4808, some c4805, some c4809, some c4807, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p11117 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11117 : lratChecker f11117 p11117 = .success := by decide +kernel
theorem unsat11117 : Unsatisfiable (PosFin 65) f11117 := by
  apply lratCheckerSound f11117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11117
  · intro a ha; simp [p11117] at ha; subst a; trivial
  · exact checked11117
theorem derived11117 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11117 := by
  apply localUnsat_implies_entails f11117 [c4808, c4805, c4809, c4807] c11117 unsat11117 (by rfl) a
  have h0 : Entails.eval a c4808 := h 4807 (by decide)
  have h1 : Entails.eval a c4805 := h 4804 (by decide)
  have h2 : Entails.eval a c4809 := h 4808 (by decide)
  have h3 : Entails.eval a c4807 := h 4806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11118 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11118 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11114, some c11108, some c11085, some c4819, some c4818, some c4835, some c4821, some c11101, some c4820, some c4842, some c11110, some c10340, some c11115, some c11116, some c11117, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11118 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11118 : lratChecker f11118 p11118 = .success := by decide +kernel
theorem unsat11118 : Unsatisfiable (PosFin 65) f11118 := by
  apply lratCheckerSound f11118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11118
  · intro a ha; simp [p11118] at ha; subst a; trivial
  · exact checked11118
theorem derived11118 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11118 := by
  apply localUnsat_implies_entails f11118 [c11018, c11114, c11108, c11085, c4819, c4818, c4835, c4821, c11101, c4820, c4842, c11110, c10340, c11115, c11116, c11117] c11118 unsat11118 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11114 := derived11114 a h
  have h2 : Entails.eval a c11108 := derived11108 a h
  have h3 : Entails.eval a c11085 := derived11085 a h
  have h4 : Entails.eval a c4819 := h 4818 (by decide)
  have h5 : Entails.eval a c4818 := h 4817 (by decide)
  have h6 : Entails.eval a c4835 := h 4834 (by decide)
  have h7 : Entails.eval a c4821 := h 4820 (by decide)
  have h8 : Entails.eval a c11101 := derived11101 a h
  have h9 : Entails.eval a c4820 := h 4819 (by decide)
  have h10 : Entails.eval a c4842 := h 4841 (by decide)
  have h11 : Entails.eval a c11110 := derived11110 a h
  have h12 : Entails.eval a c10340 := derived10340 a h
  have h13 : Entails.eval a c11115 := derived11115 a h
  have h14 : Entails.eval a c11116 := derived11116 a h
  have h15 : Entails.eval a c11117 := derived11117 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11119 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11119 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11085, some c11117, some c4794, some c4798, some c4322, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11119 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11119 : lratChecker f11119 p11119 = .success := by decide +kernel
theorem unsat11119 : Unsatisfiable (PosFin 65) f11119 := by
  apply lratCheckerSound f11119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11119
  · intro a ha; simp [p11119] at ha; subst a; trivial
  · exact checked11119
theorem derived11119 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11119 := by
  apply localUnsat_implies_entails f11119 [c11108, c11085, c11117, c4794, c4798, c4322] c11119 unsat11119 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c11117 := derived11117 a h
  have h3 : Entails.eval a c4794 := h 4793 (by decide)
  have h4 : Entails.eval a c4798 := h 4797 (by decide)
  have h5 : Entails.eval a c4322 := h 4321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11120 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨62, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11120 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11108, some c11101, some c11085, some c4822, some c4819, some c4818, some c4820, some c4835, some c4841, some c4821, some c4842, some c11110, some c11118, some c11119, some c4793, some c4797, some c4317, some c4799, some c4791, some c4815, some c4817, some c4816, some c118, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11120 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked11120 : lratChecker f11120 p11120 = .success := by decide +kernel
theorem unsat11120 : Unsatisfiable (PosFin 65) f11120 := by
  apply lratCheckerSound f11120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11120
  · intro a ha; simp [p11120] at ha; subst a; trivial
  · exact checked11120
theorem derived11120 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11120 := by
  apply localUnsat_implies_entails f11120 [c11018, c11108, c11101, c11085, c4822, c4819, c4818, c4820, c4835, c4841, c4821, c4842, c11110, c11118, c11119, c4793, c4797, c4317, c4799, c4791, c4815, c4817, c4816, c118] c11120 unsat11120 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c11085 := derived11085 a h
  have h4 : Entails.eval a c4822 := h 4821 (by decide)
  have h5 : Entails.eval a c4819 := h 4818 (by decide)
  have h6 : Entails.eval a c4818 := h 4817 (by decide)
  have h7 : Entails.eval a c4820 := h 4819 (by decide)
  have h8 : Entails.eval a c4835 := h 4834 (by decide)
  have h9 : Entails.eval a c4841 := h 4840 (by decide)
  have h10 : Entails.eval a c4821 := h 4820 (by decide)
  have h11 : Entails.eval a c4842 := h 4841 (by decide)
  have h12 : Entails.eval a c11110 := derived11110 a h
  have h13 : Entails.eval a c11118 := derived11118 a h
  have h14 : Entails.eval a c11119 := derived11119 a h
  have h15 : Entails.eval a c4793 := h 4792 (by decide)
  have h16 : Entails.eval a c4797 := h 4796 (by decide)
  have h17 : Entails.eval a c4317 := h 4316 (by decide)
  have h18 : Entails.eval a c4799 := h 4798 (by decide)
  have h19 : Entails.eval a c4791 := h 4790 (by decide)
  have h20 : Entails.eval a c4815 := h 4814 (by decide)
  have h21 : Entails.eval a c4817 := h 4816 (by decide)
  have h22 : Entails.eval a c4816 := h 4815 (by decide)
  have h23 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11121 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11121 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11101, some c10240, some c10786, some c9878, some c10255, some c9864, some c10243, some c10229, some c10242, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11121 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11121 : lratChecker f11121 p11121 = .success := by decide +kernel
theorem unsat11121 : Unsatisfiable (PosFin 65) f11121 := by
  apply lratCheckerSound f11121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11121
  · intro a ha; simp [p11121] at ha; subst a; trivial
  · exact checked11121
theorem derived11121 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11121 := by
  apply localUnsat_implies_entails f11121 [c11108, c11101, c10240, c10786, c9878, c10255, c9864, c10243, c10229, c10242] c11121 unsat11121 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c10240 := derived10240 a h
  have h3 : Entails.eval a c10786 := derived10786 a h
  have h4 : Entails.eval a c9878 := derived9878 a h
  have h5 : Entails.eval a c10255 := derived10255 a h
  have h6 : Entails.eval a c9864 := derived9864 a h
  have h7 : Entails.eval a c10243 := derived10243 a h
  have h8 : Entails.eval a c10229 := derived10229 a h
  have h9 : Entails.eval a c10242 := derived10242 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11122 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨59, by decide⟩, false), (⟨7, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11122 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11085, some c2578, some c2920, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11122 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11122 : lratChecker f11122 p11122 = .success := by decide +kernel
theorem unsat11122 : Unsatisfiable (PosFin 65) f11122 := by
  apply lratCheckerSound f11122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11122
  · intro a ha; simp [p11122] at ha; subst a; trivial
  · exact checked11122
theorem derived11122 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11122 := by
  apply localUnsat_implies_entails f11122 [c11085, c2578, c2920] c11122 unsat11122 (by rfl) a
  have h0 : Entails.eval a c11085 := derived11085 a h
  have h1 : Entails.eval a c2578 := h 2577 (by decide)
  have h2 : Entails.eval a c2920 := h 2919 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11123 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨62, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11123 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11120, some c11085, some c10226, some c10657, some c11122, some c2579, some c2921, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11123 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11123 : lratChecker f11123 p11123 = .success := by decide +kernel
theorem unsat11123 : Unsatisfiable (PosFin 65) f11123 := by
  apply lratCheckerSound f11123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11123
  · intro a ha; simp [p11123] at ha; subst a; trivial
  · exact checked11123
theorem derived11123 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11123 := by
  apply localUnsat_implies_entails f11123 [c11120, c11085, c10226, c10657, c11122, c2579, c2921] c11123 unsat11123 (by rfl) a
  have h0 : Entails.eval a c11120 := derived11120 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c10226 := derived10226 a h
  have h3 : Entails.eval a c10657 := derived10657 a h
  have h4 : Entails.eval a c11122 := derived11122 a h
  have h5 : Entails.eval a c2579 := h 2578 (by decide)
  have h6 : Entails.eval a c2921 := h 2920 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11124 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11124 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c10240, some c10718, some c10236, some c11101, some c9878, some c11121, some c10255, some c10373, some c9864, some c10382, some c10644, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11124 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11124 : lratChecker f11124 p11124 = .success := by decide +kernel
theorem unsat11124 : Unsatisfiable (PosFin 65) f11124 := by
  apply lratCheckerSound f11124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11124
  · intro a ha; simp [p11124] at ha; subst a; trivial
  · exact checked11124
theorem derived11124 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11124 := by
  apply localUnsat_implies_entails f11124 [c11108, c10240, c10718, c10236, c11101, c9878, c11121, c10255, c10373, c9864, c10382, c10644] c11124 unsat11124 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c10240 := derived10240 a h
  have h2 : Entails.eval a c10718 := derived10718 a h
  have h3 : Entails.eval a c10236 := derived10236 a h
  have h4 : Entails.eval a c11101 := derived11101 a h
  have h5 : Entails.eval a c9878 := derived9878 a h
  have h6 : Entails.eval a c11121 := derived11121 a h
  have h7 : Entails.eval a c10255 := derived10255 a h
  have h8 : Entails.eval a c10373 := derived10373 a h
  have h9 : Entails.eval a c9864 := derived9864 a h
  have h10 : Entails.eval a c10382 := derived10382 a h
  have h11 : Entails.eval a c10644 := derived10644 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11125 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11125 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10423, some c10448, some c10445, some c10796, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p11125 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11125 : lratChecker f11125 p11125 = .success := by decide +kernel
theorem unsat11125 : Unsatisfiable (PosFin 65) f11125 := by
  apply lratCheckerSound f11125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11125
  · intro a ha; simp [p11125] at ha; subst a; trivial
  · exact checked11125
theorem derived11125 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11125 := by
  apply localUnsat_implies_entails f11125 [c10423, c10448, c10445, c10796] c11125 unsat11125 (by rfl) a
  have h0 : Entails.eval a c10423 := derived10423 a h
  have h1 : Entails.eval a c10448 := derived10448 a h
  have h2 : Entails.eval a c10445 := derived10445 a h
  have h3 : Entails.eval a c10796 := derived10796 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11126 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11126 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11101, some c11120, some c11123, some c10240, some c10718, some c9878, some c10236, some c11124, some c11125, some c10826, some c10786, some c10422, some c10644, some c9864, some c10281, some c10249, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11126 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11126 : lratChecker f11126 p11126 = .success := by decide +kernel
theorem unsat11126 : Unsatisfiable (PosFin 65) f11126 := by
  apply lratCheckerSound f11126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11126
  · intro a ha; simp [p11126] at ha; subst a; trivial
  · exact checked11126
theorem derived11126 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11126 := by
  apply localUnsat_implies_entails f11126 [c11108, c11101, c11120, c11123, c10240, c10718, c9878, c10236, c11124, c11125, c10826, c10786, c10422, c10644, c9864, c10281, c10249] c11126 unsat11126 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c11120 := derived11120 a h
  have h3 : Entails.eval a c11123 := derived11123 a h
  have h4 : Entails.eval a c10240 := derived10240 a h
  have h5 : Entails.eval a c10718 := derived10718 a h
  have h6 : Entails.eval a c9878 := derived9878 a h
  have h7 : Entails.eval a c10236 := derived10236 a h
  have h8 : Entails.eval a c11124 := derived11124 a h
  have h9 : Entails.eval a c11125 := derived11125 a h
  have h10 : Entails.eval a c10826 := derived10826 a h
  have h11 : Entails.eval a c10786 := derived10786 a h
  have h12 : Entails.eval a c10422 := derived10422 a h
  have h13 : Entails.eval a c10644 := derived10644 a h
  have h14 : Entails.eval a c9864 := derived9864 a h
  have h15 : Entails.eval a c10281 := derived10281 a h
  have h16 : Entails.eval a c10249 := derived10249 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11127 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨62, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11127 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11101, some c11124, some c11125, some c10826, some c10422, some c10458, some c10530, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11127 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11127 : lratChecker f11127 p11127 = .success := by decide +kernel
theorem unsat11127 : Unsatisfiable (PosFin 65) f11127 := by
  apply lratCheckerSound f11127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11127
  · intro a ha; simp [p11127] at ha; subst a; trivial
  · exact checked11127
theorem derived11127 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11127 := by
  apply localUnsat_implies_entails f11127 [c11108, c11101, c11124, c11125, c10826, c10422, c10458, c10530] c11127 unsat11127 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c11124 := derived11124 a h
  have h3 : Entails.eval a c11125 := derived11125 a h
  have h4 : Entails.eval a c10826 := derived10826 a h
  have h5 : Entails.eval a c10422 := derived10422 a h
  have h6 : Entails.eval a c10458 := derived10458 a h
  have h7 : Entails.eval a c10530 := derived10530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11128 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨60, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11128 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10233, some c10525, some c10234, some c8300, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p11128 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11128 : lratChecker f11128 p11128 = .success := by decide +kernel
theorem unsat11128 : Unsatisfiable (PosFin 65) f11128 := by
  apply lratCheckerSound f11128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11128
  · intro a ha; simp [p11128] at ha; subst a; trivial
  · exact checked11128
theorem derived11128 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11128 := by
  apply localUnsat_implies_entails f11128 [c10233, c10525, c10234, c8300] c11128 unsat11128 (by rfl) a
  have h0 : Entails.eval a c10233 := derived10233 a h
  have h1 : Entails.eval a c10525 := derived10525 a h
  have h2 : Entails.eval a c10234 := derived10234 a h
  have h3 : Entails.eval a c8300 := derived8300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11129 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11129 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10535, some c11127, some c11128, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11129 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11129 : lratChecker f11129 p11129 = .success := by decide +kernel
theorem unsat11129 : Unsatisfiable (PosFin 65) f11129 := by
  apply lratCheckerSound f11129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11129
  · intro a ha; simp [p11129] at ha; subst a; trivial
  · exact checked11129
theorem derived11129 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11129 := by
  apply localUnsat_implies_entails f11129 [c10535, c11127, c11128] c11129 unsat11129 (by rfl) a
  have h0 : Entails.eval a c10535 := derived10535 a h
  have h1 : Entails.eval a c11127 := derived11127 a h
  have h2 : Entails.eval a c11128 := derived11128 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11130 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11130 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11101, some c11126, some c11129, some c11085, some c4832, some c4830, some c4833, some c4840, some c4820, some c8300, some c3193, some c4335, some c9742, some c3112, some c2783, some c2922, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11130 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11130 : lratChecker f11130 p11130 = .success := by decide +kernel
theorem unsat11130 : Unsatisfiable (PosFin 65) f11130 := by
  apply lratCheckerSound f11130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11130
  · intro a ha; simp [p11130] at ha; subst a; trivial
  · exact checked11130
theorem derived11130 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11130 := by
  apply localUnsat_implies_entails f11130 [c11018, c11101, c11126, c11129, c11085, c4832, c4830, c4833, c4840, c4820, c8300, c3193, c4335, c9742, c3112, c2783, c2922] c11130 unsat11130 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c11126 := derived11126 a h
  have h3 : Entails.eval a c11129 := derived11129 a h
  have h4 : Entails.eval a c11085 := derived11085 a h
  have h5 : Entails.eval a c4832 := h 4831 (by decide)
  have h6 : Entails.eval a c4830 := h 4829 (by decide)
  have h7 : Entails.eval a c4833 := h 4832 (by decide)
  have h8 : Entails.eval a c4840 := h 4839 (by decide)
  have h9 : Entails.eval a c4820 := h 4819 (by decide)
  have h10 : Entails.eval a c8300 := derived8300 a h
  have h11 : Entails.eval a c3193 := h 3192 (by decide)
  have h12 : Entails.eval a c4335 := h 4334 (by decide)
  have h13 : Entails.eval a c9742 := derived9742 a h
  have h14 : Entails.eval a c3112 := h 3111 (by decide)
  have h15 : Entails.eval a c2783 := h 2782 (by decide)
  have h16 : Entails.eval a c2922 := h 2921 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11131 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11131 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11130, some c11101, some c11126, some c11129, some c11085, some c4832, some c4830, some c4833, some c11108, some c4820, some c8300, some c3194, some c4335, some c3112, some c2958, some c3681, some c3675, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11131 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11131 : lratChecker f11131 p11131 = .success := by decide +kernel
theorem unsat11131 : Unsatisfiable (PosFin 65) f11131 := by
  apply lratCheckerSound f11131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11131
  · intro a ha; simp [p11131] at ha; subst a; trivial
  · exact checked11131
theorem derived11131 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11131 := by
  apply localUnsat_implies_entails f11131 [c11018, c11130, c11101, c11126, c11129, c11085, c4832, c4830, c4833, c11108, c4820, c8300, c3194, c4335, c3112, c2958, c3681, c3675] c11131 unsat11131 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11130 := derived11130 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c11126 := derived11126 a h
  have h4 : Entails.eval a c11129 := derived11129 a h
  have h5 : Entails.eval a c11085 := derived11085 a h
  have h6 : Entails.eval a c4832 := h 4831 (by decide)
  have h7 : Entails.eval a c4830 := h 4829 (by decide)
  have h8 : Entails.eval a c4833 := h 4832 (by decide)
  have h9 : Entails.eval a c11108 := derived11108 a h
  have h10 : Entails.eval a c4820 := h 4819 (by decide)
  have h11 : Entails.eval a c8300 := derived8300 a h
  have h12 : Entails.eval a c3194 := h 3193 (by decide)
  have h13 : Entails.eval a c4335 := h 4334 (by decide)
  have h14 : Entails.eval a c3112 := h 3111 (by decide)
  have h15 : Entails.eval a c2958 := h 2957 (by decide)
  have h16 : Entails.eval a c3681 := h 3680 (by decide)
  have h17 : Entails.eval a c3675 := h 3674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11132 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11132 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11130, some c11101, some c11126, some c11129, some c11085, some c4832, some c4830, some c4833, some c11108, some c11109, some c4353, some c3208, some c4821, some c10351, some c2958, some c3681, some c3675, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11132 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11132 : lratChecker f11132 p11132 = .success := by decide +kernel
theorem unsat11132 : Unsatisfiable (PosFin 65) f11132 := by
  apply lratCheckerSound f11132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11132
  · intro a ha; simp [p11132] at ha; subst a; trivial
  · exact checked11132
theorem derived11132 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11132 := by
  apply localUnsat_implies_entails f11132 [c11130, c11101, c11126, c11129, c11085, c4832, c4830, c4833, c11108, c11109, c4353, c3208, c4821, c10351, c2958, c3681, c3675] c11132 unsat11132 (by rfl) a
  have h0 : Entails.eval a c11130 := derived11130 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c11126 := derived11126 a h
  have h3 : Entails.eval a c11129 := derived11129 a h
  have h4 : Entails.eval a c11085 := derived11085 a h
  have h5 : Entails.eval a c4832 := h 4831 (by decide)
  have h6 : Entails.eval a c4830 := h 4829 (by decide)
  have h7 : Entails.eval a c4833 := h 4832 (by decide)
  have h8 : Entails.eval a c11108 := derived11108 a h
  have h9 : Entails.eval a c11109 := derived11109 a h
  have h10 : Entails.eval a c4353 := h 4352 (by decide)
  have h11 : Entails.eval a c3208 := h 3207 (by decide)
  have h12 : Entails.eval a c4821 := h 4820 (by decide)
  have h13 : Entails.eval a c10351 := derived10351 a h
  have h14 : Entails.eval a c2958 := h 2957 (by decide)
  have h15 : Entails.eval a c3681 := h 3680 (by decide)
  have h16 : Entails.eval a c3675 := h 3674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11133 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11133 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11108, some c11101, some c11085, some c11126, some c11129, some c4832, some c4830, some c4833, some c11130, some c4827, some c11131, some c11132, some c7994, some c8380, some c11111, some c2929, some c2603, some c2536, some c3796, some c10215, some c4693, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11133 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked11133 : lratChecker f11133 p11133 = .success := by decide +kernel
theorem unsat11133 : Unsatisfiable (PosFin 65) f11133 := by
  apply lratCheckerSound f11133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11133
  · intro a ha; simp [p11133] at ha; subst a; trivial
  · exact checked11133
theorem derived11133 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11133 := by
  apply localUnsat_implies_entails f11133 [c11108, c11101, c11085, c11126, c11129, c4832, c4830, c4833, c11130, c4827, c11131, c11132, c7994, c8380, c11111, c2929, c2603, c2536, c3796, c10215, c4693] c11133 unsat11133 (by rfl) a
  have h0 : Entails.eval a c11108 := derived11108 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c11085 := derived11085 a h
  have h3 : Entails.eval a c11126 := derived11126 a h
  have h4 : Entails.eval a c11129 := derived11129 a h
  have h5 : Entails.eval a c4832 := h 4831 (by decide)
  have h6 : Entails.eval a c4830 := h 4829 (by decide)
  have h7 : Entails.eval a c4833 := h 4832 (by decide)
  have h8 : Entails.eval a c11130 := derived11130 a h
  have h9 : Entails.eval a c4827 := h 4826 (by decide)
  have h10 : Entails.eval a c11131 := derived11131 a h
  have h11 : Entails.eval a c11132 := derived11132 a h
  have h12 : Entails.eval a c7994 := derived7994 a h
  have h13 : Entails.eval a c8380 := derived8380 a h
  have h14 : Entails.eval a c11111 := derived11111 a h
  have h15 : Entails.eval a c2929 := h 2928 (by decide)
  have h16 : Entails.eval a c2603 := h 2602 (by decide)
  have h17 : Entails.eval a c2536 := h 2535 (by decide)
  have h18 : Entails.eval a c3796 := h 3795 (by decide)
  have h19 : Entails.eval a c10215 := derived10215 a h
  have h20 : Entails.eval a c4693 := h 4692 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11134 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11134 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11108, some c11133, some c10227, some c10282, some c10207, some c10283, some c10396, some c10540, some c10228, some c8380, some c11085, some c10214, some c4353, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11134 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11134 : lratChecker f11134 p11134 = .success := by decide +kernel
theorem unsat11134 : Unsatisfiable (PosFin 65) f11134 := by
  apply lratCheckerSound f11134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11134
  · intro a ha; simp [p11134] at ha; subst a; trivial
  · exact checked11134
theorem derived11134 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11134 := by
  apply localUnsat_implies_entails f11134 [c11018, c11108, c11133, c10227, c10282, c10207, c10283, c10396, c10540, c10228, c8380, c11085, c10214, c4353] c11134 unsat11134 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c10227 := derived10227 a h
  have h4 : Entails.eval a c10282 := derived10282 a h
  have h5 : Entails.eval a c10207 := derived10207 a h
  have h6 : Entails.eval a c10283 := derived10283 a h
  have h7 : Entails.eval a c10396 := derived10396 a h
  have h8 : Entails.eval a c10540 := derived10540 a h
  have h9 : Entails.eval a c10228 := derived10228 a h
  have h10 : Entails.eval a c8380 := derived8380 a h
  have h11 : Entails.eval a c11085 := derived11085 a h
  have h12 : Entails.eval a c10214 := derived10214 a h
  have h13 : Entails.eval a c4353 := h 4352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11135 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11135 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c4209, some c10443, some c10454, some c2594, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11135 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11135 : lratChecker f11135 p11135 = .success := by decide +kernel
theorem unsat11135 : Unsatisfiable (PosFin 65) f11135 := by
  apply lratCheckerSound f11135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11135
  · intro a ha; simp [p11135] at ha; subst a; trivial
  · exact checked11135
theorem derived11135 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11135 := by
  apply localUnsat_implies_entails f11135 [c11133, c4209, c10443, c10454, c2594] c11135 unsat11135 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c4209 := h 4208 (by decide)
  have h2 : Entails.eval a c10443 := derived10443 a h
  have h3 : Entails.eval a c10454 := derived10454 a h
  have h4 : Entails.eval a c2594 := h 2593 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11136 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11136 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11085, some c11133, some c11101, some c11108, some c10282, some c10396, some c10534, some c4334, some c10227, some c10207, some c10228, some c10549, some c10556, some c4318, some c2593, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11136 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11136 : lratChecker f11136 p11136 = .success := by decide +kernel
theorem unsat11136 : Unsatisfiable (PosFin 65) f11136 := by
  apply lratCheckerSound f11136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11136
  · intro a ha; simp [p11136] at ha; subst a; trivial
  · exact checked11136
theorem derived11136 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11136 := by
  apply localUnsat_implies_entails f11136 [c11018, c11085, c11133, c11101, c11108, c10282, c10396, c10534, c4334, c10227, c10207, c10228, c10549, c10556, c4318, c2593] c11136 unsat11136 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c11101 := derived11101 a h
  have h4 : Entails.eval a c11108 := derived11108 a h
  have h5 : Entails.eval a c10282 := derived10282 a h
  have h6 : Entails.eval a c10396 := derived10396 a h
  have h7 : Entails.eval a c10534 := derived10534 a h
  have h8 : Entails.eval a c4334 := h 4333 (by decide)
  have h9 : Entails.eval a c10227 := derived10227 a h
  have h10 : Entails.eval a c10207 := derived10207 a h
  have h11 : Entails.eval a c10228 := derived10228 a h
  have h12 : Entails.eval a c10549 := derived10549 a h
  have h13 : Entails.eval a c10556 := derived10556 a h
  have h14 : Entails.eval a c4318 := h 4317 (by decide)
  have h15 : Entails.eval a c2593 := h 2592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11137 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11137 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11134, some c11133, some c11108, some c10282, some c10396, some c11101, some c11085, some c11136, some c11135, some c10545, some c4321, some c4319, some c1000, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11137 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11137 : lratChecker f11137 p11137 = .success := by decide +kernel
theorem unsat11137 : Unsatisfiable (PosFin 65) f11137 := by
  apply lratCheckerSound f11137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11137
  · intro a ha; simp [p11137] at ha; subst a; trivial
  · exact checked11137
theorem derived11137 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11137 := by
  apply localUnsat_implies_entails f11137 [c11018, c11134, c11133, c11108, c10282, c10396, c11101, c11085, c11136, c11135, c10545, c4321, c4319, c1000] c11137 unsat11137 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11134 := derived11134 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c11108 := derived11108 a h
  have h4 : Entails.eval a c10282 := derived10282 a h
  have h5 : Entails.eval a c10396 := derived10396 a h
  have h6 : Entails.eval a c11101 := derived11101 a h
  have h7 : Entails.eval a c11085 := derived11085 a h
  have h8 : Entails.eval a c11136 := derived11136 a h
  have h9 : Entails.eval a c11135 := derived11135 a h
  have h10 : Entails.eval a c10545 := derived10545 a h
  have h11 : Entails.eval a c4321 := h 4320 (by decide)
  have h12 : Entails.eval a c4319 := h 4318 (by decide)
  have h13 : Entails.eval a c1000 := h 999 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11138 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11138 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11133, some c11108, some c10227, some c10282, some c10228, some c10396, some c8380, some c10021, some c11137, some c4201, some c10545, some c4207, some c4206, some c893, some c751, some c9020, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11138 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11138 : lratChecker f11138 p11138 = .success := by decide +kernel
theorem unsat11138 : Unsatisfiable (PosFin 65) f11138 := by
  apply lratCheckerSound f11138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11138
  · intro a ha; simp [p11138] at ha; subst a; trivial
  · exact checked11138
theorem derived11138 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11138 := by
  apply localUnsat_implies_entails f11138 [c11018, c11133, c11108, c10227, c10282, c10228, c10396, c8380, c10021, c11137, c4201, c10545, c4207, c4206, c893, c751, c9020] c11138 unsat11138 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11133 := derived11133 a h
  have h2 : Entails.eval a c11108 := derived11108 a h
  have h3 : Entails.eval a c10227 := derived10227 a h
  have h4 : Entails.eval a c10282 := derived10282 a h
  have h5 : Entails.eval a c10228 := derived10228 a h
  have h6 : Entails.eval a c10396 := derived10396 a h
  have h7 : Entails.eval a c8380 := derived8380 a h
  have h8 : Entails.eval a c10021 := derived10021 a h
  have h9 : Entails.eval a c11137 := derived11137 a h
  have h10 : Entails.eval a c4201 := h 4200 (by decide)
  have h11 : Entails.eval a c10545 := derived10545 a h
  have h12 : Entails.eval a c4207 := h 4206 (by decide)
  have h13 : Entails.eval a c4206 := h 4205 (by decide)
  have h14 : Entails.eval a c893 := h 892 (by decide)
  have h15 : Entails.eval a c751 := h 750 (by decide)
  have h16 : Entails.eval a c9020 := derived9020 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11139 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11139 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11108, some c9029, some c4209, some c10443, some c743, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11139 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11139 : lratChecker f11139 p11139 = .success := by decide +kernel
theorem unsat11139 : Unsatisfiable (PosFin 65) f11139 := by
  apply lratCheckerSound f11139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11139
  · intro a ha; simp [p11139] at ha; subst a; trivial
  · exact checked11139
theorem derived11139 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11139 := by
  apply localUnsat_implies_entails f11139 [c11133, c11108, c9029, c4209, c10443, c743] c11139 unsat11139 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c9029 := derived9029 a h
  have h3 : Entails.eval a c4209 := h 4208 (by decide)
  have h4 : Entails.eval a c10443 := derived10443 a h
  have h5 : Entails.eval a c743 := h 742 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11140 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11140 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11085, some c11133, some c11101, some c11108, some c10282, some c10396, some c10534, some c4334, some c10227, some c10228, some c8380, some c10207, some c10021, some c11137, some c11138, some c11139, some c10549, some c10556, some c4318, some c4202, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11140 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked11140 : lratChecker f11140 p11140 = .success := by decide +kernel
theorem unsat11140 : Unsatisfiable (PosFin 65) f11140 := by
  apply lratCheckerSound f11140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11140
  · intro a ha; simp [p11140] at ha; subst a; trivial
  · exact checked11140
theorem derived11140 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11140 := by
  apply localUnsat_implies_entails f11140 [c11018, c11085, c11133, c11101, c11108, c10282, c10396, c10534, c4334, c10227, c10228, c8380, c10207, c10021, c11137, c11138, c11139, c10549, c10556, c4318, c4202] c11140 unsat11140 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c11101 := derived11101 a h
  have h4 : Entails.eval a c11108 := derived11108 a h
  have h5 : Entails.eval a c10282 := derived10282 a h
  have h6 : Entails.eval a c10396 := derived10396 a h
  have h7 : Entails.eval a c10534 := derived10534 a h
  have h8 : Entails.eval a c4334 := h 4333 (by decide)
  have h9 : Entails.eval a c10227 := derived10227 a h
  have h10 : Entails.eval a c10228 := derived10228 a h
  have h11 : Entails.eval a c8380 := derived8380 a h
  have h12 : Entails.eval a c10207 := derived10207 a h
  have h13 : Entails.eval a c10021 := derived10021 a h
  have h14 : Entails.eval a c11137 := derived11137 a h
  have h15 : Entails.eval a c11138 := derived11138 a h
  have h16 : Entails.eval a c11139 := derived11139 a h
  have h17 : Entails.eval a c10549 := derived10549 a h
  have h18 : Entails.eval a c10556 := derived10556 a h
  have h19 : Entails.eval a c4318 := h 4317 (by decide)
  have h20 : Entails.eval a c4202 := h 4201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11141 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11141 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11085, some c11133, some c11101, some c11108, some c10282, some c10396, some c10534, some c4334, some c10227, some c10207, some c10228, some c10549, some c10556, some c4318, some c4202, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11141 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11141 : lratChecker f11141 p11141 = .success := by decide +kernel
theorem unsat11141 : Unsatisfiable (PosFin 65) f11141 := by
  apply lratCheckerSound f11141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11141
  · intro a ha; simp [p11141] at ha; subst a; trivial
  · exact checked11141
theorem derived11141 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11141 := by
  apply localUnsat_implies_entails f11141 [c11018, c11085, c11133, c11101, c11108, c10282, c10396, c10534, c4334, c10227, c10207, c10228, c10549, c10556, c4318, c4202] c11141 unsat11141 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11085 := derived11085 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c11101 := derived11101 a h
  have h4 : Entails.eval a c11108 := derived11108 a h
  have h5 : Entails.eval a c10282 := derived10282 a h
  have h6 : Entails.eval a c10396 := derived10396 a h
  have h7 : Entails.eval a c10534 := derived10534 a h
  have h8 : Entails.eval a c4334 := h 4333 (by decide)
  have h9 : Entails.eval a c10227 := derived10227 a h
  have h10 : Entails.eval a c10207 := derived10207 a h
  have h11 : Entails.eval a c10228 := derived10228 a h
  have h12 : Entails.eval a c10549 := derived10549 a h
  have h13 : Entails.eval a c10556 := derived10556 a h
  have h14 : Entails.eval a c4318 := h 4317 (by decide)
  have h15 : Entails.eval a c4202 := h 4201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11142 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11142 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4205, some c10380, some c10614, some c4207, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11142 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11142 : lratChecker f11142 p11142 = .success := by decide +kernel
theorem unsat11142 : Unsatisfiable (PosFin 65) f11142 := by
  apply lratCheckerSound f11142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11142
  · intro a ha; simp [p11142] at ha; subst a; trivial
  · exact checked11142
theorem derived11142 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11142 := by
  apply localUnsat_implies_entails f11142 [c4205, c10380, c10614, c4207] c11142 unsat11142 (by rfl) a
  have h0 : Entails.eval a c4205 := h 4204 (by decide)
  have h1 : Entails.eval a c10380 := derived10380 a h
  have h2 : Entails.eval a c10614 := derived10614 a h
  have h3 : Entails.eval a c4207 := h 4206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11143 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11143 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11108, some c11137, some c11141, some c9029, some c11139, some c11142, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11143 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11143 : lratChecker f11143 p11143 = .success := by decide +kernel
theorem unsat11143 : Unsatisfiable (PosFin 65) f11143 := by
  apply lratCheckerSound f11143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11143
  · intro a ha; simp [p11143] at ha; subst a; trivial
  · exact checked11143
theorem derived11143 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11143 := by
  apply localUnsat_implies_entails f11143 [c11133, c11108, c11137, c11141, c9029, c11139, c11142] c11143 unsat11143 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11137 := derived11137 a h
  have h3 : Entails.eval a c11141 := derived11141 a h
  have h4 : Entails.eval a c9029 := derived9029 a h
  have h5 : Entails.eval a c11139 := derived11139 a h
  have h6 : Entails.eval a c11142 := derived11142 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11144 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11144 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11143, some c11133, some c11108, some c10282, some c10396, some c11085, some c10550, some c10545, some c10561, some c10744, some c10614, some c4328, some c4281, some c1007, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11144 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11144 : lratChecker f11144 p11144 = .success := by decide +kernel
theorem unsat11144 : Unsatisfiable (PosFin 65) f11144 := by
  apply lratCheckerSound f11144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11144
  · intro a ha; simp [p11144] at ha; subst a; trivial
  · exact checked11144
theorem derived11144 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11144 := by
  apply localUnsat_implies_entails f11144 [c11018, c11143, c11133, c11108, c10282, c10396, c11085, c10550, c10545, c10561, c10744, c10614, c4328, c4281, c1007] c11144 unsat11144 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11143 := derived11143 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c11108 := derived11108 a h
  have h4 : Entails.eval a c10282 := derived10282 a h
  have h5 : Entails.eval a c10396 := derived10396 a h
  have h6 : Entails.eval a c11085 := derived11085 a h
  have h7 : Entails.eval a c10550 := derived10550 a h
  have h8 : Entails.eval a c10545 := derived10545 a h
  have h9 : Entails.eval a c10561 := derived10561 a h
  have h10 : Entails.eval a c10744 := derived10744 a h
  have h11 : Entails.eval a c10614 := derived10614 a h
  have h12 : Entails.eval a c4328 := h 4327 (by decide)
  have h13 : Entails.eval a c4281 := h 4280 (by decide)
  have h14 : Entails.eval a c1007 := h 1006 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11145 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11145 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11144, some c11085, some c11133, some c11101, some c11108, some c10282, some c10396, some c10534, some c4334, some c11134, some c10227, some c10228, some c8380, some c11143, some c10153, some c11140, some c10207, some c10556, some c4268, some c2525, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11145 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked11145 : lratChecker f11145 p11145 = .success := by decide +kernel
theorem unsat11145 : Unsatisfiable (PosFin 65) f11145 := by
  apply lratCheckerSound f11145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11145
  · intro a ha; simp [p11145] at ha; subst a; trivial
  · exact checked11145
theorem derived11145 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11145 := by
  apply localUnsat_implies_entails f11145 [c11018, c11144, c11085, c11133, c11101, c11108, c10282, c10396, c10534, c4334, c11134, c10227, c10228, c8380, c11143, c10153, c11140, c10207, c10556, c4268, c2525] c11145 unsat11145 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11144 := derived11144 a h
  have h2 : Entails.eval a c11085 := derived11085 a h
  have h3 : Entails.eval a c11133 := derived11133 a h
  have h4 : Entails.eval a c11101 := derived11101 a h
  have h5 : Entails.eval a c11108 := derived11108 a h
  have h6 : Entails.eval a c10282 := derived10282 a h
  have h7 : Entails.eval a c10396 := derived10396 a h
  have h8 : Entails.eval a c10534 := derived10534 a h
  have h9 : Entails.eval a c4334 := h 4333 (by decide)
  have h10 : Entails.eval a c11134 := derived11134 a h
  have h11 : Entails.eval a c10227 := derived10227 a h
  have h12 : Entails.eval a c10228 := derived10228 a h
  have h13 : Entails.eval a c8380 := derived8380 a h
  have h14 : Entails.eval a c11143 := derived11143 a h
  have h15 : Entails.eval a c10153 := derived10153 a h
  have h16 : Entails.eval a c11140 := derived11140 a h
  have h17 : Entails.eval a c10207 := derived10207 a h
  have h18 : Entails.eval a c10556 := derived10556 a h
  have h19 : Entails.eval a c4268 := h 4267 (by decide)
  have h20 : Entails.eval a c2525 := h 2524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11146 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11146 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11143, some c11144, some c11145, some c9104, some c10455, some c10443, some c4277, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11146 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11146 : lratChecker f11146 p11146 = .success := by decide +kernel
theorem unsat11146 : Unsatisfiable (PosFin 65) f11146 := by
  apply lratCheckerSound f11146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11146
  · intro a ha; simp [p11146] at ha; subst a; trivial
  · exact checked11146
theorem derived11146 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11146 := by
  apply localUnsat_implies_entails f11146 [c11133, c11143, c11144, c11145, c9104, c10455, c10443, c4277] c11146 unsat11146 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11143 := derived11143 a h
  have h2 : Entails.eval a c11144 := derived11144 a h
  have h3 : Entails.eval a c11145 := derived11145 a h
  have h4 : Entails.eval a c9104 := derived9104 a h
  have h5 : Entails.eval a c10455 := derived10455 a h
  have h6 : Entails.eval a c10443 := derived10443 a h
  have h7 : Entails.eval a c4277 := h 4276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11147 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨31, by decide⟩, false), (⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11147 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c10455, some c10443, some c10598, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11147 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11147 : lratChecker f11147 p11147 = .success := by decide +kernel
theorem unsat11147 : Unsatisfiable (PosFin 65) f11147 := by
  apply lratCheckerSound f11147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11147
  · intro a ha; simp [p11147] at ha; subst a; trivial
  · exact checked11147
theorem derived11147 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11147 := by
  apply localUnsat_implies_entails f11147 [c11133, c10455, c10443, c10598] c11147 unsat11147 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c10455 := derived10455 a h
  have h2 : Entails.eval a c10443 := derived10443 a h
  have h3 : Entails.eval a c10598 := derived10598 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11148 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11148 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11147, some c10556, some c10631, some c10384, some c10687, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11148 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11148 : lratChecker f11148 p11148 = .success := by decide +kernel
theorem unsat11148 : Unsatisfiable (PosFin 65) f11148 := by
  apply lratCheckerSound f11148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11148
  · intro a ha; simp [p11148] at ha; subst a; trivial
  · exact checked11148
theorem derived11148 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11148 := by
  apply localUnsat_implies_entails f11148 [c11133, c11147, c10556, c10631, c10384, c10687] c11148 unsat11148 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11147 := derived11147 a h
  have h2 : Entails.eval a c10556 := derived10556 a h
  have h3 : Entails.eval a c10631 := derived10631 a h
  have h4 : Entails.eval a c10384 := derived10384 a h
  have h5 : Entails.eval a c10687 := derived10687 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11149 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11149 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11108, some c11101, some c10608, some c10552, some c10556, some c10631, some c10384, some c10555, some c10585, some c10561, some c10605, some c10537, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11149 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11149 : lratChecker f11149 p11149 = .success := by decide +kernel
theorem unsat11149 : Unsatisfiable (PosFin 65) f11149 := by
  apply lratCheckerSound f11149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11149
  · intro a ha; simp [p11149] at ha; subst a; trivial
  · exact checked11149
theorem derived11149 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11149 := by
  apply localUnsat_implies_entails f11149 [c11133, c11108, c11101, c10608, c10552, c10556, c10631, c10384, c10555, c10585, c10561, c10605, c10537] c11149 unsat11149 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c10608 := derived10608 a h
  have h4 : Entails.eval a c10552 := derived10552 a h
  have h5 : Entails.eval a c10556 := derived10556 a h
  have h6 : Entails.eval a c10631 := derived10631 a h
  have h7 : Entails.eval a c10384 := derived10384 a h
  have h8 : Entails.eval a c10555 := derived10555 a h
  have h9 : Entails.eval a c10585 := derived10585 a h
  have h10 : Entails.eval a c10561 := derived10561 a h
  have h11 : Entails.eval a c10605 := derived10605 a h
  have h12 : Entails.eval a c10537 := derived10537 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11150 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11150 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11101, some c11148, some c11149, some c10455, some c10438, some c10572, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11150 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11150 : lratChecker f11150 p11150 = .success := by decide +kernel
theorem unsat11150 : Unsatisfiable (PosFin 65) f11150 := by
  apply lratCheckerSound f11150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11150
  · intro a ha; simp [p11150] at ha; subst a; trivial
  · exact checked11150
theorem derived11150 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11150 := by
  apply localUnsat_implies_entails f11150 [c11133, c11101, c11148, c11149, c10455, c10438, c10572] c11150 unsat11150 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c11148 := derived11148 a h
  have h3 : Entails.eval a c11149 := derived11149 a h
  have h4 : Entails.eval a c10455 := derived10455 a h
  have h5 : Entails.eval a c10438 := derived10438 a h
  have h6 : Entails.eval a c10572 := derived10572 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived11150

end CochromaticTwenty.Certificates.FixedCore0
