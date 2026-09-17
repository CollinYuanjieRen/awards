import MerLeanExperiment.Certificates.FixedCore0.Steps0300_0399

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7951 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨37, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7951 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7950, some c6304, some c6319, some c6964, some c7150, some c7310, some c7797, some c7796, some c6, some c7790, some c7795, some c5211, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7951 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7951 : lratChecker f7951 p7951 = .success := by decide +kernel
theorem unsat7951 : Unsatisfiable (PosFin 65) f7951 := by
  apply lratCheckerSound f7951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7951
  · intro a ha; simp [p7951] at ha; subst a; trivial
  · exact checked7951
theorem derived7951 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7951 := by
  apply localUnsat_implies_entails f7951 [c7950, c6304, c6319, c6964, c7150, c7310, c7797, c7796, c6, c7790, c7795, c5211] c7951 unsat7951 (by rfl) a
  have h0 : Entails.eval a c7950 := derived7950 a h
  have h1 : Entails.eval a c6304 := h 6303 (by decide)
  have h2 : Entails.eval a c6319 := h 6318 (by decide)
  have h3 : Entails.eval a c6964 := h 6963 (by decide)
  have h4 : Entails.eval a c7150 := h 7149 (by decide)
  have h5 : Entails.eval a c7310 := h 7309 (by decide)
  have h6 : Entails.eval a c7797 := derived7797 a h
  have h7 : Entails.eval a c7796 := derived7796 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c7790 := derived7790 a h
  have h10 : Entails.eval a c7795 := derived7795 a h
  have h11 : Entails.eval a c5211 := h 5210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7952 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨37, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7952 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7149, some c6963, some c7252, some c7010, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7952 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7952 : lratChecker f7952 p7952 = .success := by decide +kernel
theorem unsat7952 : Unsatisfiable (PosFin 65) f7952 := by
  apply lratCheckerSound f7952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7952
  · intro a ha; simp [p7952] at ha; subst a; trivial
  · exact checked7952
theorem derived7952 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7952 := by
  apply localUnsat_implies_entails f7952 [c7149, c6963, c7252, c7010] c7952 unsat7952 (by rfl) a
  have h0 : Entails.eval a c7149 := h 7148 (by decide)
  have h1 : Entails.eval a c6963 := h 6962 (by decide)
  have h2 : Entails.eval a c7252 := h 7251 (by decide)
  have h3 : Entails.eval a c7010 := h 7009 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7953 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7953 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c7877, some c7950, some c7951, some c6318, some c7952, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7953 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7953 : lratChecker f7953 p7953 = .success := by decide +kernel
theorem unsat7953 : Unsatisfiable (PosFin 65) f7953 := by
  apply lratCheckerSound f7953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7953
  · intro a ha; simp [p7953] at ha; subst a; trivial
  · exact checked7953
theorem derived7953 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7953 := by
  apply localUnsat_implies_entails f7953 [c7921, c7877, c7950, c7951, c6318, c7952] c7953 unsat7953 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c7877 := derived7877 a h
  have h2 : Entails.eval a c7950 := derived7950 a h
  have h3 : Entails.eval a c7951 := derived7951 a h
  have h4 : Entails.eval a c6318 := h 6317 (by decide)
  have h5 : Entails.eval a c7952 := derived7952 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7954 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7954 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5209, some c5154, some c5224, some c5411, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7954 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7954 : lratChecker f7954 p7954 = .success := by decide +kernel
theorem unsat7954 : Unsatisfiable (PosFin 65) f7954 := by
  apply lratCheckerSound f7954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7954
  · intro a ha; simp [p7954] at ha; subst a; trivial
  · exact checked7954
theorem derived7954 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7954 := by
  apply localUnsat_implies_entails f7954 [c5209, c5154, c5224, c5411] c7954 unsat7954 (by rfl) a
  have h0 : Entails.eval a c5209 := h 5208 (by decide)
  have h1 : Entails.eval a c5154 := h 5153 (by decide)
  have h2 : Entails.eval a c5224 := h 5223 (by decide)
  have h3 : Entails.eval a c5411 := h 5410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7955 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨19, by decide⟩, true), (⟨47, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7955 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6332, some c7010, some c7474, some c7342, some c7954, some c5706, some c5732, some c64, some c5240, some c5250, some c6100, some c5328, some c5777, some c5, some c85, some c1729, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7955 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7955 : lratChecker f7955 p7955 = .success := by decide +kernel
theorem unsat7955 : Unsatisfiable (PosFin 65) f7955 := by
  apply lratCheckerSound f7955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7955
  · intro a ha; simp [p7955] at ha; subst a; trivial
  · exact checked7955
theorem derived7955 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7955 := by
  apply localUnsat_implies_entails f7955 [c6332, c7010, c7474, c7342, c7954, c5706, c5732, c64, c5240, c5250, c6100, c5328, c5777, c5, c85, c1729] c7955 unsat7955 (by rfl) a
  have h0 : Entails.eval a c6332 := h 6331 (by decide)
  have h1 : Entails.eval a c7010 := h 7009 (by decide)
  have h2 : Entails.eval a c7474 := h 7473 (by decide)
  have h3 : Entails.eval a c7342 := h 7341 (by decide)
  have h4 : Entails.eval a c7954 := derived7954 a h
  have h5 : Entails.eval a c5706 := h 5705 (by decide)
  have h6 : Entails.eval a c5732 := h 5731 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c5240 := h 5239 (by decide)
  have h9 : Entails.eval a c5250 := h 5249 (by decide)
  have h10 : Entails.eval a c6100 := h 6099 (by decide)
  have h11 : Entails.eval a c5328 := h 5327 (by decide)
  have h12 : Entails.eval a c5777 := h 5776 (by decide)
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c1729 := h 1728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7956 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨44, by decide⟩, true), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7956 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6978, some c7066, some c7121, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7956 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7956 : lratChecker f7956 p7956 = .success := by decide +kernel
theorem unsat7956 : Unsatisfiable (PosFin 65) f7956 := by
  apply lratCheckerSound f7956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7956
  · intro a ha; simp [p7956] at ha; subst a; trivial
  · exact checked7956
theorem derived7956 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7956 := by
  apply localUnsat_implies_entails f7956 [c6978, c7066, c7121] c7956 unsat7956 (by rfl) a
  have h0 : Entails.eval a c6978 := h 6977 (by decide)
  have h1 : Entails.eval a c7066 := h 7065 (by decide)
  have h2 : Entails.eval a c7121 := h 7120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7957 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7957 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7956, some c6860, some c7941, some c7955, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7957 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7957 : lratChecker f7957 p7957 = .success := by decide +kernel
theorem unsat7957 : Unsatisfiable (PosFin 65) f7957 := by
  apply lratCheckerSound f7957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7957
  · intro a ha; simp [p7957] at ha; subst a; trivial
  · exact checked7957
theorem derived7957 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7957 := by
  apply localUnsat_implies_entails f7957 [c7956, c6860, c7941, c7955] c7957 unsat7957 (by rfl) a
  have h0 : Entails.eval a c7956 := derived7956 a h
  have h1 : Entails.eval a c6860 := h 6859 (by decide)
  have h2 : Entails.eval a c7941 := derived7941 a h
  have h3 : Entails.eval a c7955 := derived7955 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7958 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨47, by decide⟩, false), (⟨64, by decide⟩, false), (⟨48, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7958 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5507, some c5699, some c5722, some c5607, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7958 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7958 : lratChecker f7958 p7958 = .success := by decide +kernel
theorem unsat7958 : Unsatisfiable (PosFin 65) f7958 := by
  apply lratCheckerSound f7958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7958
  · intro a ha; simp [p7958] at ha; subst a; trivial
  · exact checked7958
theorem derived7958 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7958 := by
  apply localUnsat_implies_entails f7958 [c5507, c5699, c5722, c5607] c7958 unsat7958 (by rfl) a
  have h0 : Entails.eval a c5507 := h 5506 (by decide)
  have h1 : Entails.eval a c5699 := h 5698 (by decide)
  have h2 : Entails.eval a c5722 := h 5721 (by decide)
  have h3 : Entails.eval a c5607 := h 5606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7959 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨48, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7959 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c6332, some c7046, some c7474, some c7958, some c5154, some c5236, some c5823, some c5398, some c5361, some c6035, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7959 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7959 : lratChecker f7959 p7959 = .success := by decide +kernel
theorem unsat7959 : Unsatisfiable (PosFin 65) f7959 := by
  apply lratCheckerSound f7959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7959
  · intro a ha; simp [p7959] at ha; subst a; trivial
  · exact checked7959
theorem derived7959 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7959 := by
  apply localUnsat_implies_entails f7959 [c7877, c7921, c6332, c7046, c7474, c7958, c5154, c5236, c5823, c5398, c5361, c6035] c7959 unsat7959 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c6332 := h 6331 (by decide)
  have h3 : Entails.eval a c7046 := h 7045 (by decide)
  have h4 : Entails.eval a c7474 := h 7473 (by decide)
  have h5 : Entails.eval a c7958 := derived7958 a h
  have h6 : Entails.eval a c5154 := h 5153 (by decide)
  have h7 : Entails.eval a c5236 := h 5235 (by decide)
  have h8 : Entails.eval a c5823 := h 5822 (by decide)
  have h9 : Entails.eval a c5398 := h 5397 (by decide)
  have h10 : Entails.eval a c5361 := h 5360 (by decide)
  have h11 : Entails.eval a c6035 := h 6034 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7960 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7960 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c7953, some c7956, some c7947, some c6332, some c7957, some c7384, some c7121, some c7914, some c7342, some c7046, some c7474, some c7959, some c5140, some c5179, some c5206, some c5351, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7960 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7960 : lratChecker f7960 p7960 = .success := by decide +kernel
theorem unsat7960 : Unsatisfiable (PosFin 65) f7960 := by
  apply lratCheckerSound f7960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7960
  · intro a ha; simp [p7960] at ha; subst a; trivial
  · exact checked7960
theorem derived7960 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7960 := by
  apply localUnsat_implies_entails f7960 [c7877, c7921, c7953, c7956, c7947, c6332, c7957, c7384, c7121, c7914, c7342, c7046, c7474, c7959, c5140, c5179, c5206, c5351] c7960 unsat7960 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7953 := derived7953 a h
  have h3 : Entails.eval a c7956 := derived7956 a h
  have h4 : Entails.eval a c7947 := derived7947 a h
  have h5 : Entails.eval a c6332 := h 6331 (by decide)
  have h6 : Entails.eval a c7957 := derived7957 a h
  have h7 : Entails.eval a c7384 := h 7383 (by decide)
  have h8 : Entails.eval a c7121 := h 7120 (by decide)
  have h9 : Entails.eval a c7914 := derived7914 a h
  have h10 : Entails.eval a c7342 := h 7341 (by decide)
  have h11 : Entails.eval a c7046 := h 7045 (by decide)
  have h12 : Entails.eval a c7474 := h 7473 (by decide)
  have h13 : Entails.eval a c7959 := derived7959 a h
  have h14 : Entails.eval a c5140 := h 5139 (by decide)
  have h15 : Entails.eval a c5179 := h 5178 (by decide)
  have h16 : Entails.eval a c5206 := h 5205 (by decide)
  have h17 : Entails.eval a c5351 := h 5350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7961 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨50, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7961 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7953, some c7921, some c7877, some c7956, some c7960, some c7946, some c6436, some c6406, some c7046, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7961 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7961 : lratChecker f7961 p7961 = .success := by decide +kernel
theorem unsat7961 : Unsatisfiable (PosFin 65) f7961 := by
  apply lratCheckerSound f7961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7961
  · intro a ha; simp [p7961] at ha; subst a; trivial
  · exact checked7961
theorem derived7961 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7961 := by
  apply localUnsat_implies_entails f7961 [c7953, c7921, c7877, c7956, c7960, c7946, c6436, c6406, c7046] c7961 unsat7961 (by rfl) a
  have h0 : Entails.eval a c7953 := derived7953 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c7956 := derived7956 a h
  have h4 : Entails.eval a c7960 := derived7960 a h
  have h5 : Entails.eval a c7946 := derived7946 a h
  have h6 : Entails.eval a c6436 := h 6435 (by decide)
  have h7 : Entails.eval a c6406 := h 6405 (by decide)
  have h8 : Entails.eval a c7046 := h 7045 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7962 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7962 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7953, some c7921, some c7877, some c7961, some c6318, some c6942, some c7946, some c6477, some c6436, some c7162, some c7046, some c7822, some c6525, some c6822, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7962 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7962 : lratChecker f7962 p7962 = .success := by decide +kernel
theorem unsat7962 : Unsatisfiable (PosFin 65) f7962 := by
  apply lratCheckerSound f7962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7962
  · intro a ha; simp [p7962] at ha; subst a; trivial
  · exact checked7962
theorem derived7962 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7962 := by
  apply localUnsat_implies_entails f7962 [c7953, c7921, c7877, c7961, c6318, c6942, c7946, c6477, c6436, c7162, c7046, c7822, c6525, c6822] c7962 unsat7962 (by rfl) a
  have h0 : Entails.eval a c7953 := derived7953 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c7961 := derived7961 a h
  have h4 : Entails.eval a c6318 := h 6317 (by decide)
  have h5 : Entails.eval a c6942 := h 6941 (by decide)
  have h6 : Entails.eval a c7946 := derived7946 a h
  have h7 : Entails.eval a c6477 := h 6476 (by decide)
  have h8 : Entails.eval a c6436 := h 6435 (by decide)
  have h9 : Entails.eval a c7162 := h 7161 (by decide)
  have h10 : Entails.eval a c7046 := h 7045 (by decide)
  have h11 : Entails.eval a c7822 := derived7822 a h
  have h12 : Entails.eval a c6525 := h 6524 (by decide)
  have h13 : Entails.eval a c6822 := h 6821 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7963 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7963 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7953, some c7962, some c7826, some c6801, some c6818, some c7945, some c7326, some c6319, some c7413, some c7067, some c7797, some c7796, some c6, some c7790, some c7795, some c5211, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7963 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7963 : lratChecker f7963 p7963 = .success := by decide +kernel
theorem unsat7963 : Unsatisfiable (PosFin 65) f7963 := by
  apply lratCheckerSound f7963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7963
  · intro a ha; simp [p7963] at ha; subst a; trivial
  · exact checked7963
theorem derived7963 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7963 := by
  apply localUnsat_implies_entails f7963 [c7953, c7962, c7826, c6801, c6818, c7945, c7326, c6319, c7413, c7067, c7797, c7796, c6, c7790, c7795, c5211] c7963 unsat7963 (by rfl) a
  have h0 : Entails.eval a c7953 := derived7953 a h
  have h1 : Entails.eval a c7962 := derived7962 a h
  have h2 : Entails.eval a c7826 := derived7826 a h
  have h3 : Entails.eval a c6801 := h 6800 (by decide)
  have h4 : Entails.eval a c6818 := h 6817 (by decide)
  have h5 : Entails.eval a c7945 := derived7945 a h
  have h6 : Entails.eval a c7326 := h 7325 (by decide)
  have h7 : Entails.eval a c6319 := h 6318 (by decide)
  have h8 : Entails.eval a c7413 := h 7412 (by decide)
  have h9 : Entails.eval a c7067 := h 7066 (by decide)
  have h10 : Entails.eval a c7797 := derived7797 a h
  have h11 : Entails.eval a c7796 := derived7796 a h
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c7790 := derived7790 a h
  have h14 : Entails.eval a c7795 := derived7795 a h
  have h15 : Entails.eval a c5211 := h 5210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7964 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7964 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6349, some c7413, some c7797, some c7796, some c6, some c7790, some c7795, some c5211, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7964 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7964 : lratChecker f7964 p7964 = .success := by decide +kernel
theorem unsat7964 : Unsatisfiable (PosFin 65) f7964 := by
  apply lratCheckerSound f7964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7964
  · intro a ha; simp [p7964] at ha; subst a; trivial
  · exact checked7964
theorem derived7964 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7964 := by
  apply localUnsat_implies_entails f7964 [c6349, c7413, c7797, c7796, c6, c7790, c7795, c5211] c7964 unsat7964 (by rfl) a
  have h0 : Entails.eval a c6349 := h 6348 (by decide)
  have h1 : Entails.eval a c7413 := h 7412 (by decide)
  have h2 : Entails.eval a c7797 := derived7797 a h
  have h3 : Entails.eval a c7796 := derived7796 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c7790 := derived7790 a h
  have h6 : Entails.eval a c7795 := derived7795 a h
  have h7 : Entails.eval a c5211 := h 5210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7965 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨44, by decide⟩, true), (⟨64, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7965 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6964, some c7067, some c7826, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7965 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7965 : lratChecker f7965 p7965 = .success := by decide +kernel
theorem unsat7965 : Unsatisfiable (PosFin 65) f7965 := by
  apply lratCheckerSound f7965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7965
  · intro a ha; simp [p7965] at ha; subst a; trivial
  · exact checked7965
theorem derived7965 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7965 := by
  apply localUnsat_implies_entails f7965 [c6964, c7067, c7826] c7965 unsat7965 (by rfl) a
  have h0 : Entails.eval a c6964 := h 6963 (by decide)
  have h1 : Entails.eval a c7067 := h 7066 (by decide)
  have h2 : Entails.eval a c7826 := derived7826 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7966 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7966 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7963, some c7826, some c7136, some c6908, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7966 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7966 : lratChecker f7966 p7966 = .success := by decide +kernel
theorem unsat7966 : Unsatisfiable (PosFin 65) f7966 := by
  apply lratCheckerSound f7966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7966
  · intro a ha; simp [p7966] at ha; subst a; trivial
  · exact checked7966
theorem derived7966 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7966 := by
  apply localUnsat_implies_entails f7966 [c7963, c7826, c7136, c6908] c7966 unsat7966 (by rfl) a
  have h0 : Entails.eval a c7963 := derived7963 a h
  have h1 : Entails.eval a c7826 := derived7826 a h
  have h2 : Entails.eval a c7136 := h 7135 (by decide)
  have h3 : Entails.eval a c6908 := h 6907 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7967 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7967 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7965, some c7921, some c7877, some c7964, some c7966, some c7150, some c7733, some c7007, some c7019, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7967 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7967 : lratChecker f7967 p7967 = .success := by decide +kernel
theorem unsat7967 : Unsatisfiable (PosFin 65) f7967 := by
  apply lratCheckerSound f7967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7967
  · intro a ha; simp [p7967] at ha; subst a; trivial
  · exact checked7967
theorem derived7967 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7967 := by
  apply localUnsat_implies_entails f7967 [c7965, c7921, c7877, c7964, c7966, c7150, c7733, c7007, c7019] c7967 unsat7967 (by rfl) a
  have h0 : Entails.eval a c7965 := derived7965 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c7964 := derived7964 a h
  have h4 : Entails.eval a c7966 := derived7966 a h
  have h5 : Entails.eval a c7150 := h 7149 (by decide)
  have h6 : Entails.eval a c7733 := derived7733 a h
  have h7 : Entails.eval a c7007 := h 7006 (by decide)
  have h8 : Entails.eval a c7019 := h 7018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7968 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7968 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7963, some c7921, some c7965, some c7967, some c7310, some c6832, some c7096, some c6349, some c6517, some c7734, some c7179, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7968 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7968 : lratChecker f7968 p7968 = .success := by decide +kernel
theorem unsat7968 : Unsatisfiable (PosFin 65) f7968 := by
  apply lratCheckerSound f7968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7968
  · intro a ha; simp [p7968] at ha; subst a; trivial
  · exact checked7968
theorem derived7968 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7968 := by
  apply localUnsat_implies_entails f7968 [c7963, c7921, c7965, c7967, c7310, c6832, c7096, c6349, c6517, c7734, c7179] c7968 unsat7968 (by rfl) a
  have h0 : Entails.eval a c7963 := derived7963 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7965 := derived7965 a h
  have h3 : Entails.eval a c7967 := derived7967 a h
  have h4 : Entails.eval a c7310 := h 7309 (by decide)
  have h5 : Entails.eval a c6832 := h 6831 (by decide)
  have h6 : Entails.eval a c7096 := h 7095 (by decide)
  have h7 : Entails.eval a c6349 := h 6348 (by decide)
  have h8 : Entails.eval a c6517 := h 6516 (by decide)
  have h9 : Entails.eval a c7734 := derived7734 a h
  have h10 : Entails.eval a c7179 := h 7178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7969 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7969 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7963, some c7826, some c6908, some c6878, some c7163, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7969 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7969 : lratChecker f7969 p7969 = .success := by decide +kernel
theorem unsat7969 : Unsatisfiable (PosFin 65) f7969 := by
  apply lratCheckerSound f7969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7969
  · intro a ha; simp [p7969] at ha; subst a; trivial
  · exact checked7969
theorem derived7969 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7969 := by
  apply localUnsat_implies_entails f7969 [c7963, c7826, c6908, c6878, c7163] c7969 unsat7969 (by rfl) a
  have h0 : Entails.eval a c7963 := derived7963 a h
  have h1 : Entails.eval a c7826 := derived7826 a h
  have h2 : Entails.eval a c6908 := h 6907 (by decide)
  have h3 : Entails.eval a c6878 := h 6877 (by decide)
  have h4 : Entails.eval a c7163 := h 7162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7970 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7970 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7968, some c7963, some c7527, some c7483, some c6894, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7970 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7970 : lratChecker f7970 p7970 = .success := by decide +kernel
theorem unsat7970 : Unsatisfiable (PosFin 65) f7970 := by
  apply lratCheckerSound f7970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7970
  · intro a ha; simp [p7970] at ha; subst a; trivial
  · exact checked7970
theorem derived7970 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7970 := by
  apply localUnsat_implies_entails f7970 [c7968, c7963, c7527, c7483, c6894] c7970 unsat7970 (by rfl) a
  have h0 : Entails.eval a c7968 := derived7968 a h
  have h1 : Entails.eval a c7963 := derived7963 a h
  have h2 : Entails.eval a c7527 := h 7526 (by decide)
  have h3 : Entails.eval a c7483 := h 7482 (by decide)
  have h4 : Entails.eval a c6894 := h 6893 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7971 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7971 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7963, some c7970, some c6908, some c6832, some c6894, some c7294, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7971 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7971 : lratChecker f7971 p7971 = .success := by decide +kernel
theorem unsat7971 : Unsatisfiable (PosFin 65) f7971 := by
  apply lratCheckerSound f7971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7971
  · intro a ha; simp [p7971] at ha; subst a; trivial
  · exact checked7971
theorem derived7971 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7971 := by
  apply localUnsat_implies_entails f7971 [c7963, c7970, c6908, c6832, c6894, c7294] c7971 unsat7971 (by rfl) a
  have h0 : Entails.eval a c7963 := derived7963 a h
  have h1 : Entails.eval a c7970 := derived7970 a h
  have h2 : Entails.eval a c6908 := h 6907 (by decide)
  have h3 : Entails.eval a c6832 := h 6831 (by decide)
  have h4 : Entails.eval a c6894 := h 6893 (by decide)
  have h5 : Entails.eval a c7294 := h 7293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7972 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨36, by decide⟩, false), (⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7972 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7229, some c7043, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7972 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7972 : lratChecker f7972 p7972 = .success := by decide +kernel
theorem unsat7972 : Unsatisfiable (PosFin 65) f7972 := by
  apply lratCheckerSound f7972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7972
  · intro a ha; simp [p7972] at ha; subst a; trivial
  · exact checked7972
theorem derived7972 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7972 := by
  apply localUnsat_implies_entails f7972 [c7229, c7043] c7972 unsat7972 (by rfl) a
  have h0 : Entails.eval a c7229 := h 7228 (by decide)
  have h1 : Entails.eval a c7043 := h 7042 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7973 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨42, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, true), (⟨44, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7973 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6289, some c6634, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7973 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7973 : lratChecker f7973 p7973 = .success := by decide +kernel
theorem unsat7973 : Unsatisfiable (PosFin 65) f7973 := by
  apply lratCheckerSound f7973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7973
  · intro a ha; simp [p7973] at ha; subst a; trivial
  · exact checked7973
theorem derived7973 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7973 := by
  apply localUnsat_implies_entails f7973 [c6289, c6634] c7973 unsat7973 (by rfl) a
  have h0 : Entails.eval a c6289 := h 6288 (by decide)
  have h1 : Entails.eval a c6634 := h 6633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7974 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7974 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7968, some c7970, some c7971, some c7494, some c6517, some c6504, some c7963, some c6908, some c6498, some c3716, some c3481, some c3526, some c3864, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7974 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7974 : lratChecker f7974 p7974 = .success := by decide +kernel
theorem unsat7974 : Unsatisfiable (PosFin 65) f7974 := by
  apply lratCheckerSound f7974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7974
  · intro a ha; simp [p7974] at ha; subst a; trivial
  · exact checked7974
theorem derived7974 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7974 := by
  apply localUnsat_implies_entails f7974 [c7968, c7970, c7971, c7494, c6517, c6504, c7963, c6908, c6498, c3716, c3481, c3526, c3864] c7974 unsat7974 (by rfl) a
  have h0 : Entails.eval a c7968 := derived7968 a h
  have h1 : Entails.eval a c7970 := derived7970 a h
  have h2 : Entails.eval a c7971 := derived7971 a h
  have h3 : Entails.eval a c7494 := h 7493 (by decide)
  have h4 : Entails.eval a c6517 := h 6516 (by decide)
  have h5 : Entails.eval a c6504 := h 6503 (by decide)
  have h6 : Entails.eval a c7963 := derived7963 a h
  have h7 : Entails.eval a c6908 := h 6907 (by decide)
  have h8 : Entails.eval a c6498 := h 6497 (by decide)
  have h9 : Entails.eval a c3716 := h 3715 (by decide)
  have h10 : Entails.eval a c3481 := h 3480 (by decide)
  have h11 : Entails.eval a c3526 := h 3525 (by decide)
  have h12 : Entails.eval a c3864 := h 3863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7975 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨1, by decide⟩, true), (⟨39, by decide⟩, true), (⟨56, by decide⟩, false), (⟨60, by decide⟩, false), (⟨34, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨35, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7975 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1030, some c1058, some c2058, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7975 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7975 : lratChecker f7975 p7975 = .success := by decide +kernel
theorem unsat7975 : Unsatisfiable (PosFin 65) f7975 := by
  apply lratCheckerSound f7975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7975
  · intro a ha; simp [p7975] at ha; subst a; trivial
  · exact checked7975
theorem derived7975 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7975 := by
  apply localUnsat_implies_entails f7975 [c1030, c1058, c2058] c7975 unsat7975 (by rfl) a
  have h0 : Entails.eval a c1030 := h 1029 (by decide)
  have h1 : Entails.eval a c1058 := h 1057 (by decide)
  have h2 : Entails.eval a c2058 := h 2057 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7976 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7976 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7968, some c7970, some c7971, some c7494, some c6517, some c6504, some c7969, some c6637, some c7921, some c7963, some c6589, some c7877, some c7973, some c7972, some c6753, some c7108, some c6908, some c6498, some c6721, some c6713, some c7326, some c6588, some c7273, some c7796, some c7975, some c7974, some c3569, some c3609, some c4213, some c4488, some c2315, some c3936, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7976 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked7976 : lratChecker f7976 p7976 = .success := by decide +kernel
theorem unsat7976 : Unsatisfiable (PosFin 65) f7976 := by
  apply lratCheckerSound f7976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7976
  · intro a ha; simp [p7976] at ha; subst a; trivial
  · exact checked7976
theorem derived7976 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7976 := by
  apply localUnsat_implies_entails f7976 [c7968, c7970, c7971, c7494, c6517, c6504, c7969, c6637, c7921, c7963, c6589, c7877, c7973, c7972, c6753, c7108, c6908, c6498, c6721, c6713, c7326, c6588, c7273, c7796, c7975, c7974, c3569, c3609, c4213, c4488, c2315, c3936] c7976 unsat7976 (by rfl) a
  have h0 : Entails.eval a c7968 := derived7968 a h
  have h1 : Entails.eval a c7970 := derived7970 a h
  have h2 : Entails.eval a c7971 := derived7971 a h
  have h3 : Entails.eval a c7494 := h 7493 (by decide)
  have h4 : Entails.eval a c6517 := h 6516 (by decide)
  have h5 : Entails.eval a c6504 := h 6503 (by decide)
  have h6 : Entails.eval a c7969 := derived7969 a h
  have h7 : Entails.eval a c6637 := h 6636 (by decide)
  have h8 : Entails.eval a c7921 := derived7921 a h
  have h9 : Entails.eval a c7963 := derived7963 a h
  have h10 : Entails.eval a c6589 := h 6588 (by decide)
  have h11 : Entails.eval a c7877 := derived7877 a h
  have h12 : Entails.eval a c7973 := derived7973 a h
  have h13 : Entails.eval a c7972 := derived7972 a h
  have h14 : Entails.eval a c6753 := h 6752 (by decide)
  have h15 : Entails.eval a c7108 := h 7107 (by decide)
  have h16 : Entails.eval a c6908 := h 6907 (by decide)
  have h17 : Entails.eval a c6498 := h 6497 (by decide)
  have h18 : Entails.eval a c6721 := h 6720 (by decide)
  have h19 : Entails.eval a c6713 := h 6712 (by decide)
  have h20 : Entails.eval a c7326 := h 7325 (by decide)
  have h21 : Entails.eval a c6588 := h 6587 (by decide)
  have h22 : Entails.eval a c7273 := h 7272 (by decide)
  have h23 : Entails.eval a c7796 := derived7796 a h
  have h24 : Entails.eval a c7975 := derived7975 a h
  have h25 : Entails.eval a c7974 := derived7974 a h
  have h26 : Entails.eval a c3569 := h 3568 (by decide)
  have h27 : Entails.eval a c3609 := h 3608 (by decide)
  have h28 : Entails.eval a c4213 := h 4212 (by decide)
  have h29 : Entails.eval a c4488 := h 4487 (by decide)
  have h30 : Entails.eval a c2315 := h 2314 (by decide)
  have h31 : Entails.eval a c3936 := h 3935 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7977 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7977 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7969, some c7971, some c7968, some c7970, some c7494, some c6517, some c6504, some c7877, some c7921, some c7973, some c7972, some c7229, some c7963, some c6908, some c6498, some c6637, some c6589, some c6753, some c6721, some c6713, some c6588, some c7108, some c7976, some c447, some c6, some c719, some c4608, some c7974, some c7790, some c3569, some c3609, some c286, some c3370, some c7958, some c264, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7977 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked7977 : lratChecker f7977 p7977 = .success := by decide +kernel
theorem unsat7977 : Unsatisfiable (PosFin 65) f7977 := by
  apply lratCheckerSound f7977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7977
  · intro a ha; simp [p7977] at ha; subst a; trivial
  · exact checked7977
theorem derived7977 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7977 := by
  apply localUnsat_implies_entails f7977 [c7969, c7971, c7968, c7970, c7494, c6517, c6504, c7877, c7921, c7973, c7972, c7229, c7963, c6908, c6498, c6637, c6589, c6753, c6721, c6713, c6588, c7108, c7976, c447, c6, c719, c4608, c7974, c7790, c3569, c3609, c286, c3370, c7958, c264] c7977 unsat7977 (by rfl) a
  have h0 : Entails.eval a c7969 := derived7969 a h
  have h1 : Entails.eval a c7971 := derived7971 a h
  have h2 : Entails.eval a c7968 := derived7968 a h
  have h3 : Entails.eval a c7970 := derived7970 a h
  have h4 : Entails.eval a c7494 := h 7493 (by decide)
  have h5 : Entails.eval a c6517 := h 6516 (by decide)
  have h6 : Entails.eval a c6504 := h 6503 (by decide)
  have h7 : Entails.eval a c7877 := derived7877 a h
  have h8 : Entails.eval a c7921 := derived7921 a h
  have h9 : Entails.eval a c7973 := derived7973 a h
  have h10 : Entails.eval a c7972 := derived7972 a h
  have h11 : Entails.eval a c7229 := h 7228 (by decide)
  have h12 : Entails.eval a c7963 := derived7963 a h
  have h13 : Entails.eval a c6908 := h 6907 (by decide)
  have h14 : Entails.eval a c6498 := h 6497 (by decide)
  have h15 : Entails.eval a c6637 := h 6636 (by decide)
  have h16 : Entails.eval a c6589 := h 6588 (by decide)
  have h17 : Entails.eval a c6753 := h 6752 (by decide)
  have h18 : Entails.eval a c6721 := h 6720 (by decide)
  have h19 : Entails.eval a c6713 := h 6712 (by decide)
  have h20 : Entails.eval a c6588 := h 6587 (by decide)
  have h21 : Entails.eval a c7108 := h 7107 (by decide)
  have h22 : Entails.eval a c7976 := derived7976 a h
  have h23 : Entails.eval a c447 := h 446 (by decide)
  have h24 : Entails.eval a c6 := h 5 (by decide)
  have h25 : Entails.eval a c719 := h 718 (by decide)
  have h26 : Entails.eval a c4608 := h 4607 (by decide)
  have h27 : Entails.eval a c7974 := derived7974 a h
  have h28 : Entails.eval a c7790 := derived7790 a h
  have h29 : Entails.eval a c3569 := h 3568 (by decide)
  have h30 : Entails.eval a c3609 := h 3608 (by decide)
  have h31 : Entails.eval a c286 := h 285 (by decide)
  have h32 : Entails.eval a c3370 := h 3369 (by decide)
  have h33 : Entails.eval a c7958 := derived7958 a h
  have h34 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7978 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7978 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7968, some c7971, some c7877, some c7921, some c7969, some c7970, some c7494, some c6517, some c6504, some c7973, some c7977, some c6683, some c7963, some c6908, some c6283, some c6292, some c6498, some c7326, some c6644, some c6281, some c6280, some c6, some c441, some c1421, some c7790, some c4626, some c4444, some c286, some c347, some c7792, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7978 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked7978 : lratChecker f7978 p7978 = .success := by decide +kernel
theorem unsat7978 : Unsatisfiable (PosFin 65) f7978 := by
  apply lratCheckerSound f7978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7978
  · intro a ha; simp [p7978] at ha; subst a; trivial
  · exact checked7978
theorem derived7978 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7978 := by
  apply localUnsat_implies_entails f7978 [c7968, c7971, c7877, c7921, c7969, c7970, c7494, c6517, c6504, c7973, c7977, c6683, c7963, c6908, c6283, c6292, c6498, c7326, c6644, c6281, c6280, c6, c441, c1421, c7790, c4626, c4444, c286, c347, c7792] c7978 unsat7978 (by rfl) a
  have h0 : Entails.eval a c7968 := derived7968 a h
  have h1 : Entails.eval a c7971 := derived7971 a h
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c7921 := derived7921 a h
  have h4 : Entails.eval a c7969 := derived7969 a h
  have h5 : Entails.eval a c7970 := derived7970 a h
  have h6 : Entails.eval a c7494 := h 7493 (by decide)
  have h7 : Entails.eval a c6517 := h 6516 (by decide)
  have h8 : Entails.eval a c6504 := h 6503 (by decide)
  have h9 : Entails.eval a c7973 := derived7973 a h
  have h10 : Entails.eval a c7977 := derived7977 a h
  have h11 : Entails.eval a c6683 := h 6682 (by decide)
  have h12 : Entails.eval a c7963 := derived7963 a h
  have h13 : Entails.eval a c6908 := h 6907 (by decide)
  have h14 : Entails.eval a c6283 := h 6282 (by decide)
  have h15 : Entails.eval a c6292 := h 6291 (by decide)
  have h16 : Entails.eval a c6498 := h 6497 (by decide)
  have h17 : Entails.eval a c7326 := h 7325 (by decide)
  have h18 : Entails.eval a c6644 := h 6643 (by decide)
  have h19 : Entails.eval a c6281 := h 6280 (by decide)
  have h20 : Entails.eval a c6280 := h 6279 (by decide)
  have h21 : Entails.eval a c6 := h 5 (by decide)
  have h22 : Entails.eval a c441 := h 440 (by decide)
  have h23 : Entails.eval a c1421 := h 1420 (by decide)
  have h24 : Entails.eval a c7790 := derived7790 a h
  have h25 : Entails.eval a c4626 := h 4625 (by decide)
  have h26 : Entails.eval a c4444 := h 4443 (by decide)
  have h27 : Entails.eval a c286 := h 285 (by decide)
  have h28 : Entails.eval a c347 := h 346 (by decide)
  have h29 : Entails.eval a c7792 := derived7792 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7979 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7979 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7970, some c7968, some c7971, some c7494, some c6517, some c7921, some c7963, some c6908, some c7977, some c6283, some c6281, some c7969, some c6504, some c7877, some c7973, some c7972, some c6280, some c7108, some c6683, some c6498, some c7326, some c6644, some c7978, some c7796, some c3574, some c3610, some c4212, some c4487, some c2313, some c3935, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7979 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked7979 : lratChecker f7979 p7979 = .success := by decide +kernel
theorem unsat7979 : Unsatisfiable (PosFin 65) f7979 := by
  apply lratCheckerSound f7979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7979
  · intro a ha; simp [p7979] at ha; subst a; trivial
  · exact checked7979
theorem derived7979 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7979 := by
  apply localUnsat_implies_entails f7979 [c7970, c7968, c7971, c7494, c6517, c7921, c7963, c6908, c7977, c6283, c6281, c7969, c6504, c7877, c7973, c7972, c6280, c7108, c6683, c6498, c7326, c6644, c7978, c7796, c3574, c3610, c4212, c4487, c2313, c3935] c7979 unsat7979 (by rfl) a
  have h0 : Entails.eval a c7970 := derived7970 a h
  have h1 : Entails.eval a c7968 := derived7968 a h
  have h2 : Entails.eval a c7971 := derived7971 a h
  have h3 : Entails.eval a c7494 := h 7493 (by decide)
  have h4 : Entails.eval a c6517 := h 6516 (by decide)
  have h5 : Entails.eval a c7921 := derived7921 a h
  have h6 : Entails.eval a c7963 := derived7963 a h
  have h7 : Entails.eval a c6908 := h 6907 (by decide)
  have h8 : Entails.eval a c7977 := derived7977 a h
  have h9 : Entails.eval a c6283 := h 6282 (by decide)
  have h10 : Entails.eval a c6281 := h 6280 (by decide)
  have h11 : Entails.eval a c7969 := derived7969 a h
  have h12 : Entails.eval a c6504 := h 6503 (by decide)
  have h13 : Entails.eval a c7877 := derived7877 a h
  have h14 : Entails.eval a c7973 := derived7973 a h
  have h15 : Entails.eval a c7972 := derived7972 a h
  have h16 : Entails.eval a c6280 := h 6279 (by decide)
  have h17 : Entails.eval a c7108 := h 7107 (by decide)
  have h18 : Entails.eval a c6683 := h 6682 (by decide)
  have h19 : Entails.eval a c6498 := h 6497 (by decide)
  have h20 : Entails.eval a c7326 := h 7325 (by decide)
  have h21 : Entails.eval a c6644 := h 6643 (by decide)
  have h22 : Entails.eval a c7978 := derived7978 a h
  have h23 : Entails.eval a c7796 := derived7796 a h
  have h24 : Entails.eval a c3574 := h 3573 (by decide)
  have h25 : Entails.eval a c3610 := h 3609 (by decide)
  have h26 : Entails.eval a c4212 := h 4211 (by decide)
  have h27 : Entails.eval a c4487 := h 4486 (by decide)
  have h28 : Entails.eval a c2313 := h 2312 (by decide)
  have h29 : Entails.eval a c3935 := h 3934 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7980 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false), (⟨56, by decide⟩, false), (⟨34, by decide⟩, false), (⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7980 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c729, some c1029, some c1057, some c2057, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7980 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7980 : lratChecker f7980 p7980 = .success := by decide +kernel
theorem unsat7980 : Unsatisfiable (PosFin 65) f7980 := by
  apply lratCheckerSound f7980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7980
  · intro a ha; simp [p7980] at ha; subst a; trivial
  · exact checked7980
theorem derived7980 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7980 := by
  apply localUnsat_implies_entails f7980 [c729, c1029, c1057, c2057] c7980 unsat7980 (by rfl) a
  have h0 : Entails.eval a c729 := h 728 (by decide)
  have h1 : Entails.eval a c1029 := h 1028 (by decide)
  have h2 : Entails.eval a c1057 := h 1056 (by decide)
  have h3 : Entails.eval a c2057 := h 2056 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7981 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7981 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7963, some c7921, some c7877, some c7968, some c7969, some c7970, some c6908, some c7971, some c7494, some c6517, some c6498, some c6504, some c7326, some c7973, some c7229, some c7977, some c6283, some c6280, some c6281, some c6683, some c6644, some c7980, some c7979, some c3715, some c3481, some c3526, some c3862, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7981 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked7981 : lratChecker f7981 p7981 = .success := by decide +kernel
theorem unsat7981 : Unsatisfiable (PosFin 65) f7981 := by
  apply lratCheckerSound f7981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7981
  · intro a ha; simp [p7981] at ha; subst a; trivial
  · exact checked7981
theorem derived7981 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7981 := by
  apply localUnsat_implies_entails f7981 [c7963, c7921, c7877, c7968, c7969, c7970, c6908, c7971, c7494, c6517, c6498, c6504, c7326, c7973, c7229, c7977, c6283, c6280, c6281, c6683, c6644, c7980, c7979, c3715, c3481, c3526, c3862] c7981 unsat7981 (by rfl) a
  have h0 : Entails.eval a c7963 := derived7963 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c7968 := derived7968 a h
  have h4 : Entails.eval a c7969 := derived7969 a h
  have h5 : Entails.eval a c7970 := derived7970 a h
  have h6 : Entails.eval a c6908 := h 6907 (by decide)
  have h7 : Entails.eval a c7971 := derived7971 a h
  have h8 : Entails.eval a c7494 := h 7493 (by decide)
  have h9 : Entails.eval a c6517 := h 6516 (by decide)
  have h10 : Entails.eval a c6498 := h 6497 (by decide)
  have h11 : Entails.eval a c6504 := h 6503 (by decide)
  have h12 : Entails.eval a c7326 := h 7325 (by decide)
  have h13 : Entails.eval a c7973 := derived7973 a h
  have h14 : Entails.eval a c7229 := h 7228 (by decide)
  have h15 : Entails.eval a c7977 := derived7977 a h
  have h16 : Entails.eval a c6283 := h 6282 (by decide)
  have h17 : Entails.eval a c6280 := h 6279 (by decide)
  have h18 : Entails.eval a c6281 := h 6280 (by decide)
  have h19 : Entails.eval a c6683 := h 6682 (by decide)
  have h20 : Entails.eval a c6644 := h 6643 (by decide)
  have h21 : Entails.eval a c7980 := derived7980 a h
  have h22 : Entails.eval a c7979 := derived7979 a h
  have h23 : Entails.eval a c3715 := h 3714 (by decide)
  have h24 : Entails.eval a c3481 := h 3480 (by decide)
  have h25 : Entails.eval a c3526 := h 3525 (by decide)
  have h26 : Entails.eval a c3862 := h 3861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7982 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7982 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3479, some c3524, some c3730, some c3874, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7982 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7982 : lratChecker f7982 p7982 = .success := by decide +kernel
theorem unsat7982 : Unsatisfiable (PosFin 65) f7982 := by
  apply lratCheckerSound f7982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7982
  · intro a ha; simp [p7982] at ha; subst a; trivial
  · exact checked7982
theorem derived7982 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7982 := by
  apply localUnsat_implies_entails f7982 [c3479, c3524, c3730, c3874] c7982 unsat7982 (by rfl) a
  have h0 : Entails.eval a c3479 := h 3478 (by decide)
  have h1 : Entails.eval a c3524 := h 3523 (by decide)
  have h2 : Entails.eval a c3730 := h 3729 (by decide)
  have h3 : Entails.eval a c3874 := h 3873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7983 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7983 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3874, some c3951, some c3011, some c3768, some c4663, some c3200, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7983 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7983 : lratChecker f7983 p7983 = .success := by decide +kernel
theorem unsat7983 : Unsatisfiable (PosFin 65) f7983 := by
  apply lratCheckerSound f7983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7983
  · intro a ha; simp [p7983] at ha; subst a; trivial
  · exact checked7983
theorem derived7983 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7983 := by
  apply localUnsat_implies_entails f7983 [c3874, c3951, c3011, c3768, c4663, c3200] c7983 unsat7983 (by rfl) a
  have h0 : Entails.eval a c3874 := h 3873 (by decide)
  have h1 : Entails.eval a c3951 := h 3950 (by decide)
  have h2 : Entails.eval a c3011 := h 3010 (by decide)
  have h3 : Entails.eval a c3768 := h 3767 (by decide)
  have h4 : Entails.eval a c4663 := h 4662 (by decide)
  have h5 : Entails.eval a c3200 := h 3199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7984 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7984 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6907, some c6876, some c6784, some c7028, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7984 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7984 : lratChecker f7984 p7984 = .success := by decide +kernel
theorem unsat7984 : Unsatisfiable (PosFin 65) f7984 := by
  apply lratCheckerSound f7984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7984
  · intro a ha; simp [p7984] at ha; subst a; trivial
  · exact checked7984
theorem derived7984 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7984 := by
  apply localUnsat_implies_entails f7984 [c6907, c6876, c6784, c7028] c7984 unsat7984 (by rfl) a
  have h0 : Entails.eval a c6907 := h 6906 (by decide)
  have h1 : Entails.eval a c6876 := h 6875 (by decide)
  have h2 : Entails.eval a c6784 := h 6783 (by decide)
  have h3 : Entails.eval a c7028 := h 7027 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7985 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7985 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7982, some c7984, some c7983, some c3507, some c3437, some c4518, some c3011, some c3451, some c540, some c552, some c6842, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7985 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7985 : lratChecker f7985 p7985 = .success := by decide +kernel
theorem unsat7985 : Unsatisfiable (PosFin 65) f7985 := by
  apply lratCheckerSound f7985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7985
  · intro a ha; simp [p7985] at ha; subst a; trivial
  · exact checked7985
theorem derived7985 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7985 := by
  apply localUnsat_implies_entails f7985 [c7982, c7984, c7983, c3507, c3437, c4518, c3011, c3451, c540, c552, c6842] c7985 unsat7985 (by rfl) a
  have h0 : Entails.eval a c7982 := derived7982 a h
  have h1 : Entails.eval a c7984 := derived7984 a h
  have h2 : Entails.eval a c7983 := derived7983 a h
  have h3 : Entails.eval a c3507 := h 3506 (by decide)
  have h4 : Entails.eval a c3437 := h 3436 (by decide)
  have h5 : Entails.eval a c4518 := h 4517 (by decide)
  have h6 : Entails.eval a c3011 := h 3010 (by decide)
  have h7 : Entails.eval a c3451 := h 3450 (by decide)
  have h8 : Entails.eval a c540 := h 539 (by decide)
  have h9 : Entails.eval a c552 := h 551 (by decide)
  have h10 : Entails.eval a c6842 := h 6841 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7986 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7986 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c7963, some c7981, some c7877, some c7984, some c7982, some c7985, some c2951, some c1277, some c3437, some c1729, some c1887, some c3507, some c3768, some c4954, some c552, some c527, some c2005, some c6842, some c6923, some c6950, some c6389, some c1026, some c7301, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7986 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked7986 : lratChecker f7986 p7986 = .success := by decide +kernel
theorem unsat7986 : Unsatisfiable (PosFin 65) f7986 := by
  apply lratCheckerSound f7986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7986
  · intro a ha; simp [p7986] at ha; subst a; trivial
  · exact checked7986
theorem derived7986 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7986 := by
  apply localUnsat_implies_entails f7986 [c7921, c7963, c7981, c7877, c7984, c7982, c7985, c2951, c1277, c3437, c1729, c1887, c3507, c3768, c4954, c552, c527, c2005, c6842, c6923, c6950, c6389, c1026, c7301] c7986 unsat7986 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c7963 := derived7963 a h
  have h2 : Entails.eval a c7981 := derived7981 a h
  have h3 : Entails.eval a c7877 := derived7877 a h
  have h4 : Entails.eval a c7984 := derived7984 a h
  have h5 : Entails.eval a c7982 := derived7982 a h
  have h6 : Entails.eval a c7985 := derived7985 a h
  have h7 : Entails.eval a c2951 := h 2950 (by decide)
  have h8 : Entails.eval a c1277 := h 1276 (by decide)
  have h9 : Entails.eval a c3437 := h 3436 (by decide)
  have h10 : Entails.eval a c1729 := h 1728 (by decide)
  have h11 : Entails.eval a c1887 := h 1886 (by decide)
  have h12 : Entails.eval a c3507 := h 3506 (by decide)
  have h13 : Entails.eval a c3768 := h 3767 (by decide)
  have h14 : Entails.eval a c4954 := h 4953 (by decide)
  have h15 : Entails.eval a c552 := h 551 (by decide)
  have h16 : Entails.eval a c527 := h 526 (by decide)
  have h17 : Entails.eval a c2005 := h 2004 (by decide)
  have h18 : Entails.eval a c6842 := h 6841 (by decide)
  have h19 : Entails.eval a c6923 := h 6922 (by decide)
  have h20 : Entails.eval a c6950 := h 6949 (by decide)
  have h21 : Entails.eval a c6389 := h 6388 (by decide)
  have h22 : Entails.eval a c1026 := h 1025 (by decide)
  have h23 : Entails.eval a c7301 := h 7300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7987 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, false), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7987 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1729, some c1887, some c3685, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7987 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7987 : lratChecker f7987 p7987 = .success := by decide +kernel
theorem unsat7987 : Unsatisfiable (PosFin 65) f7987 := by
  apply lratCheckerSound f7987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7987
  · intro a ha; simp [p7987] at ha; subst a; trivial
  · exact checked7987
theorem derived7987 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7987 := by
  apply localUnsat_implies_entails f7987 [c1729, c1887, c3685] c7987 unsat7987 (by rfl) a
  have h0 : Entails.eval a c1729 := h 1728 (by decide)
  have h1 : Entails.eval a c1887 := h 1886 (by decide)
  have h2 : Entails.eval a c3685 := h 3684 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7988 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7988 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6389, some c6373, some c6361, some c7438, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7988 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7988 : lratChecker f7988 p7988 = .success := by decide +kernel
theorem unsat7988 : Unsatisfiable (PosFin 65) f7988 := by
  apply lratCheckerSound f7988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7988
  · intro a ha; simp [p7988] at ha; subst a; trivial
  · exact checked7988
theorem derived7988 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7988 := by
  apply localUnsat_implies_entails f7988 [c6389, c6373, c6361, c7438] c7988 unsat7988 (by rfl) a
  have h0 : Entails.eval a c6389 := h 6388 (by decide)
  have h1 : Entails.eval a c6373 := h 6372 (by decide)
  have h2 : Entails.eval a c6361 := h 6360 (by decide)
  have h3 : Entails.eval a c7438 := h 7437 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7989 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨62, by decide⟩, true), (⟨35, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7989 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6772, some c6842, some c6831, some c7046, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7989 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7989 : lratChecker f7989 p7989 = .success := by decide +kernel
theorem unsat7989 : Unsatisfiable (PosFin 65) f7989 := by
  apply lratCheckerSound f7989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7989
  · intro a ha; simp [p7989] at ha; subst a; trivial
  · exact checked7989
theorem derived7989 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7989 := by
  apply localUnsat_implies_entails f7989 [c6772, c6842, c6831, c7046] c7989 unsat7989 (by rfl) a
  have h0 : Entails.eval a c6772 := h 6771 (by decide)
  have h1 : Entails.eval a c6842 := h 6841 (by decide)
  have h2 : Entails.eval a c6831 := h 6830 (by decide)
  have h3 : Entails.eval a c7046 := h 7045 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7990 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨4, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7990 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7121, some c7988, some c7952, some c7987, some c1415, some c4445, some c446, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7990 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7990 : lratChecker f7990 p7990 = .success := by decide +kernel
theorem unsat7990 : Unsatisfiable (PosFin 65) f7990 := by
  apply lratCheckerSound f7990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7990
  · intro a ha; simp [p7990] at ha; subst a; trivial
  · exact checked7990
theorem derived7990 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7990 := by
  apply localUnsat_implies_entails f7990 [c7121, c7988, c7952, c7987, c1415, c4445, c446] c7990 unsat7990 (by rfl) a
  have h0 : Entails.eval a c7121 := h 7120 (by decide)
  have h1 : Entails.eval a c7988 := derived7988 a h
  have h2 : Entails.eval a c7952 := derived7952 a h
  have h3 : Entails.eval a c7987 := derived7987 a h
  have h4 : Entails.eval a c1415 := h 1414 (by decide)
  have h5 : Entails.eval a c4445 := h 4444 (by decide)
  have h6 : Entails.eval a c446 := h 445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7991 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7991 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c7981, some c7963, some c7984, some c7989, some c7121, some c7293, some c7217, some c7952, some c7988, some c7973, some c7986, some c6650, some c6920, some c7990, some c64, some c540, some c6710, some c1022, some c7770, some c6742, some c4852, some c5, some c1558, some c2351, some c4069, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7991 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked7991 : lratChecker f7991 p7991 = .success := by decide +kernel
theorem unsat7991 : Unsatisfiable (PosFin 65) f7991 := by
  apply lratCheckerSound f7991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7991
  · intro a ha; simp [p7991] at ha; subst a; trivial
  · exact checked7991
theorem derived7991 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7991 := by
  apply localUnsat_implies_entails f7991 [c7877, c7921, c7981, c7963, c7984, c7989, c7121, c7293, c7217, c7952, c7988, c7973, c7986, c6650, c6920, c7990, c64, c540, c6710, c1022, c7770, c6742, c4852, c5, c1558, c2351, c4069] c7991 unsat7991 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7981 := derived7981 a h
  have h3 : Entails.eval a c7963 := derived7963 a h
  have h4 : Entails.eval a c7984 := derived7984 a h
  have h5 : Entails.eval a c7989 := derived7989 a h
  have h6 : Entails.eval a c7121 := h 7120 (by decide)
  have h7 : Entails.eval a c7293 := h 7292 (by decide)
  have h8 : Entails.eval a c7217 := h 7216 (by decide)
  have h9 : Entails.eval a c7952 := derived7952 a h
  have h10 : Entails.eval a c7988 := derived7988 a h
  have h11 : Entails.eval a c7973 := derived7973 a h
  have h12 : Entails.eval a c7986 := derived7986 a h
  have h13 : Entails.eval a c6650 := h 6649 (by decide)
  have h14 : Entails.eval a c6920 := h 6919 (by decide)
  have h15 : Entails.eval a c7990 := derived7990 a h
  have h16 : Entails.eval a c64 := h 63 (by decide)
  have h17 : Entails.eval a c540 := h 539 (by decide)
  have h18 : Entails.eval a c6710 := h 6709 (by decide)
  have h19 : Entails.eval a c1022 := h 1021 (by decide)
  have h20 : Entails.eval a c7770 := derived7770 a h
  have h21 : Entails.eval a c6742 := h 6741 (by decide)
  have h22 : Entails.eval a c4852 := h 4851 (by decide)
  have h23 : Entails.eval a c5 := h 4 (by decide)
  have h24 : Entails.eval a c1558 := h 1557 (by decide)
  have h25 : Entails.eval a c2351 := h 2350 (by decide)
  have h26 : Entails.eval a c4069 := h 4068 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7992 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7992 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c7981, some c7963, some c7984, some c7989, some c7121, some c7988, some c7293, some c7952, some c7973, some c7991, some c6586, some c6497, some c6893, some c6923, some c6637, some c7507, some c7046, some c6566, some c7217, some c7438, some c117, some c1023, some c540, some c7770, some c4853, some c5, some c1035, some c3629, some c2320, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7992 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked7992 : lratChecker f7992 p7992 = .success := by decide +kernel
theorem unsat7992 : Unsatisfiable (PosFin 65) f7992 := by
  apply lratCheckerSound f7992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7992
  · intro a ha; simp [p7992] at ha; subst a; trivial
  · exact checked7992
theorem derived7992 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7992 := by
  apply localUnsat_implies_entails f7992 [c7877, c7921, c7981, c7963, c7984, c7989, c7121, c7988, c7293, c7952, c7973, c7991, c6586, c6497, c6893, c6923, c6637, c7507, c7046, c6566, c7217, c7438, c117, c1023, c540, c7770, c4853, c5, c1035, c3629, c2320] c7992 unsat7992 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7981 := derived7981 a h
  have h3 : Entails.eval a c7963 := derived7963 a h
  have h4 : Entails.eval a c7984 := derived7984 a h
  have h5 : Entails.eval a c7989 := derived7989 a h
  have h6 : Entails.eval a c7121 := h 7120 (by decide)
  have h7 : Entails.eval a c7988 := derived7988 a h
  have h8 : Entails.eval a c7293 := h 7292 (by decide)
  have h9 : Entails.eval a c7952 := derived7952 a h
  have h10 : Entails.eval a c7973 := derived7973 a h
  have h11 : Entails.eval a c7991 := derived7991 a h
  have h12 : Entails.eval a c6586 := h 6585 (by decide)
  have h13 : Entails.eval a c6497 := h 6496 (by decide)
  have h14 : Entails.eval a c6893 := h 6892 (by decide)
  have h15 : Entails.eval a c6923 := h 6922 (by decide)
  have h16 : Entails.eval a c6637 := h 6636 (by decide)
  have h17 : Entails.eval a c7507 := h 7506 (by decide)
  have h18 : Entails.eval a c7046 := h 7045 (by decide)
  have h19 : Entails.eval a c6566 := h 6565 (by decide)
  have h20 : Entails.eval a c7217 := h 7216 (by decide)
  have h21 : Entails.eval a c7438 := h 7437 (by decide)
  have h22 : Entails.eval a c117 := h 116 (by decide)
  have h23 : Entails.eval a c1023 := h 1022 (by decide)
  have h24 : Entails.eval a c540 := h 539 (by decide)
  have h25 : Entails.eval a c7770 := derived7770 a h
  have h26 : Entails.eval a c4853 := h 4852 (by decide)
  have h27 : Entails.eval a c5 := h 4 (by decide)
  have h28 : Entails.eval a c1035 := h 1034 (by decide)
  have h29 : Entails.eval a c3629 := h 3628 (by decide)
  have h30 : Entails.eval a c2320 := h 2319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7993 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7993 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c7963, some c7981, some c7984, some c7989, some c7293, some c7121, some c7952, some c7988, some c7973, some c7991, some c6586, some c6637, some c6923, some c6893, some c7046, some c6606, some c6589, some c7992, some c7987, some c728, some c1414, some c4446, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7993 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked7993 : lratChecker f7993 p7993 = .success := by decide +kernel
theorem unsat7993 : Unsatisfiable (PosFin 65) f7993 := by
  apply lratCheckerSound f7993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7993
  · intro a ha; simp [p7993] at ha; subst a; trivial
  · exact checked7993
theorem derived7993 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7993 := by
  apply localUnsat_implies_entails f7993 [c7877, c7921, c7963, c7981, c7984, c7989, c7293, c7121, c7952, c7988, c7973, c7991, c6586, c6637, c6923, c6893, c7046, c6606, c6589, c7992, c7987, c728, c1414, c4446] c7993 unsat7993 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7963 := derived7963 a h
  have h3 : Entails.eval a c7981 := derived7981 a h
  have h4 : Entails.eval a c7984 := derived7984 a h
  have h5 : Entails.eval a c7989 := derived7989 a h
  have h6 : Entails.eval a c7293 := h 7292 (by decide)
  have h7 : Entails.eval a c7121 := h 7120 (by decide)
  have h8 : Entails.eval a c7952 := derived7952 a h
  have h9 : Entails.eval a c7988 := derived7988 a h
  have h10 : Entails.eval a c7973 := derived7973 a h
  have h11 : Entails.eval a c7991 := derived7991 a h
  have h12 : Entails.eval a c6586 := h 6585 (by decide)
  have h13 : Entails.eval a c6637 := h 6636 (by decide)
  have h14 : Entails.eval a c6923 := h 6922 (by decide)
  have h15 : Entails.eval a c6893 := h 6892 (by decide)
  have h16 : Entails.eval a c7046 := h 7045 (by decide)
  have h17 : Entails.eval a c6606 := h 6605 (by decide)
  have h18 : Entails.eval a c6589 := h 6588 (by decide)
  have h19 : Entails.eval a c7992 := derived7992 a h
  have h20 : Entails.eval a c7987 := derived7987 a h
  have h21 : Entails.eval a c728 := h 727 (by decide)
  have h22 : Entails.eval a c1414 := h 1413 (by decide)
  have h23 : Entails.eval a c4446 := h 4445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7994 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7994 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c7963, some c7981, some c7984, some c7989, some c7121, some c7293, some c7952, some c7988, some c7973, some c6893, some c7217, some c7991, some c6923, some c7046, some c7438, some c6637, some c6589, some c6586, some c6606, some c6566, some c6497, some c7993, some c7982, some c728, some c7975, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7994 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked7994 : lratChecker f7994 p7994 = .success := by decide +kernel
theorem unsat7994 : Unsatisfiable (PosFin 65) f7994 := by
  apply lratCheckerSound f7994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7994
  · intro a ha; simp [p7994] at ha; subst a; trivial
  · exact checked7994
theorem derived7994 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7994 := by
  apply localUnsat_implies_entails f7994 [c7877, c7921, c7963, c7981, c7984, c7989, c7121, c7293, c7952, c7988, c7973, c6893, c7217, c7991, c6923, c7046, c7438, c6637, c6589, c6586, c6606, c6566, c6497, c7993, c7982, c728, c7975] c7994 unsat7994 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7963 := derived7963 a h
  have h3 : Entails.eval a c7981 := derived7981 a h
  have h4 : Entails.eval a c7984 := derived7984 a h
  have h5 : Entails.eval a c7989 := derived7989 a h
  have h6 : Entails.eval a c7121 := h 7120 (by decide)
  have h7 : Entails.eval a c7293 := h 7292 (by decide)
  have h8 : Entails.eval a c7952 := derived7952 a h
  have h9 : Entails.eval a c7988 := derived7988 a h
  have h10 : Entails.eval a c7973 := derived7973 a h
  have h11 : Entails.eval a c6893 := h 6892 (by decide)
  have h12 : Entails.eval a c7217 := h 7216 (by decide)
  have h13 : Entails.eval a c7991 := derived7991 a h
  have h14 : Entails.eval a c6923 := h 6922 (by decide)
  have h15 : Entails.eval a c7046 := h 7045 (by decide)
  have h16 : Entails.eval a c7438 := h 7437 (by decide)
  have h17 : Entails.eval a c6637 := h 6636 (by decide)
  have h18 : Entails.eval a c6589 := h 6588 (by decide)
  have h19 : Entails.eval a c6586 := h 6585 (by decide)
  have h20 : Entails.eval a c6606 := h 6605 (by decide)
  have h21 : Entails.eval a c6566 := h 6565 (by decide)
  have h22 : Entails.eval a c6497 := h 6496 (by decide)
  have h23 : Entails.eval a c7993 := derived7993 a h
  have h24 : Entails.eval a c7982 := derived7982 a h
  have h25 : Entails.eval a c728 := h 727 (by decide)
  have h26 : Entails.eval a c7975 := derived7975 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7995 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7995 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7984, some c7989, some c7293, some c6923, some c6893, some c7046, some c7121, some c7217, some c7988, some c7952, some c7982, some c7985, some c549, some c446, some c1718, some c1722, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p7995 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7995 : lratChecker f7995 p7995 = .success := by decide +kernel
theorem unsat7995 : Unsatisfiable (PosFin 65) f7995 := by
  apply lratCheckerSound f7995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7995
  · intro a ha; simp [p7995] at ha; subst a; trivial
  · exact checked7995
theorem derived7995 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7995 := by
  apply localUnsat_implies_entails f7995 [c7984, c7989, c7293, c6923, c6893, c7046, c7121, c7217, c7988, c7952, c7982, c7985, c549, c446, c1718, c1722] c7995 unsat7995 (by rfl) a
  have h0 : Entails.eval a c7984 := derived7984 a h
  have h1 : Entails.eval a c7989 := derived7989 a h
  have h2 : Entails.eval a c7293 := h 7292 (by decide)
  have h3 : Entails.eval a c6923 := h 6922 (by decide)
  have h4 : Entails.eval a c6893 := h 6892 (by decide)
  have h5 : Entails.eval a c7046 := h 7045 (by decide)
  have h6 : Entails.eval a c7121 := h 7120 (by decide)
  have h7 : Entails.eval a c7217 := h 7216 (by decide)
  have h8 : Entails.eval a c7988 := derived7988 a h
  have h9 : Entails.eval a c7952 := derived7952 a h
  have h10 : Entails.eval a c7982 := derived7982 a h
  have h11 : Entails.eval a c7985 := derived7985 a h
  have h12 : Entails.eval a c549 := h 548 (by decide)
  have h13 : Entails.eval a c446 := h 445 (by decide)
  have h14 : Entails.eval a c1718 := h 1717 (by decide)
  have h15 : Entails.eval a c1722 := h 1721 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7996 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7996 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7995, some c7984, some c7989, some c7121, some c7293, some c7217, some c7987, some c540, some c545, some c4859, some c3647, some c3685, some c2320, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p7996 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7996 : lratChecker f7996 p7996 = .success := by decide +kernel
theorem unsat7996 : Unsatisfiable (PosFin 65) f7996 := by
  apply lratCheckerSound f7996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7996
  · intro a ha; simp [p7996] at ha; subst a; trivial
  · exact checked7996
theorem derived7996 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7996 := by
  apply localUnsat_implies_entails f7996 [c7995, c7984, c7989, c7121, c7293, c7217, c7987, c540, c545, c4859, c3647, c3685, c2320] c7996 unsat7996 (by rfl) a
  have h0 : Entails.eval a c7995 := derived7995 a h
  have h1 : Entails.eval a c7984 := derived7984 a h
  have h2 : Entails.eval a c7989 := derived7989 a h
  have h3 : Entails.eval a c7121 := h 7120 (by decide)
  have h4 : Entails.eval a c7293 := h 7292 (by decide)
  have h5 : Entails.eval a c7217 := h 7216 (by decide)
  have h6 : Entails.eval a c7987 := derived7987 a h
  have h7 : Entails.eval a c540 := h 539 (by decide)
  have h8 : Entails.eval a c545 := h 544 (by decide)
  have h9 : Entails.eval a c4859 := h 4858 (by decide)
  have h10 : Entails.eval a c3647 := h 3646 (by decide)
  have h11 : Entails.eval a c3685 := h 3684 (by decide)
  have h12 : Entails.eval a c2320 := h 2319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7997 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7997 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7984, some c7989, some c7121, some c7293, some c7952, some c7988, some c6893, some c7995, some c7996, some c1368, some c440, some c446, some c5, some c4625, some c3616, some c3381, some c4493, some c3200, some c64, some c4859, some c5372, some c85, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7997 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked7997 : lratChecker f7997 p7997 = .success := by decide +kernel
theorem unsat7997 : Unsatisfiable (PosFin 65) f7997 := by
  apply lratCheckerSound f7997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7997
  · intro a ha; simp [p7997] at ha; subst a; trivial
  · exact checked7997
theorem derived7997 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7997 := by
  apply localUnsat_implies_entails f7997 [c7984, c7989, c7121, c7293, c7952, c7988, c6893, c7995, c7996, c1368, c440, c446, c5, c4625, c3616, c3381, c4493, c3200, c64, c4859, c5372, c85] c7997 unsat7997 (by rfl) a
  have h0 : Entails.eval a c7984 := derived7984 a h
  have h1 : Entails.eval a c7989 := derived7989 a h
  have h2 : Entails.eval a c7121 := h 7120 (by decide)
  have h3 : Entails.eval a c7293 := h 7292 (by decide)
  have h4 : Entails.eval a c7952 := derived7952 a h
  have h5 : Entails.eval a c7988 := derived7988 a h
  have h6 : Entails.eval a c6893 := h 6892 (by decide)
  have h7 : Entails.eval a c7995 := derived7995 a h
  have h8 : Entails.eval a c7996 := derived7996 a h
  have h9 : Entails.eval a c1368 := h 1367 (by decide)
  have h10 : Entails.eval a c440 := h 439 (by decide)
  have h11 : Entails.eval a c446 := h 445 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c4625 := h 4624 (by decide)
  have h14 : Entails.eval a c3616 := h 3615 (by decide)
  have h15 : Entails.eval a c3381 := h 3380 (by decide)
  have h16 : Entails.eval a c4493 := h 4492 (by decide)
  have h17 : Entails.eval a c3200 := h 3199 (by decide)
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c4859 := h 4858 (by decide)
  have h20 : Entails.eval a c5372 := h 5371 (by decide)
  have h21 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7998 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7998 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7997, some c3381, some c4224, some c420, some c468, some c7948, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p7998 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7998 : lratChecker f7998 p7998 = .success := by decide +kernel
theorem unsat7998 : Unsatisfiable (PosFin 65) f7998 := by
  apply lratCheckerSound f7998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7998
  · intro a ha; simp [p7998] at ha; subst a; trivial
  · exact checked7998
theorem derived7998 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7998 := by
  apply localUnsat_implies_entails f7998 [c7997, c3381, c4224, c420, c468, c7948] c7998 unsat7998 (by rfl) a
  have h0 : Entails.eval a c7997 := derived7997 a h
  have h1 : Entails.eval a c3381 := h 3380 (by decide)
  have h2 : Entails.eval a c4224 := h 4223 (by decide)
  have h3 : Entails.eval a c420 := h 419 (by decide)
  have h4 : Entails.eval a c468 := h 467 (by decide)
  have h5 : Entails.eval a c7948 := derived7948 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7999 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7999 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7997, some c1368, some c7998, some c3616, some c3685, some c3287, some c1277, some c420, some c3980, some c7948, some c468, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p7999 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7999 : lratChecker f7999 p7999 = .success := by decide +kernel
theorem unsat7999 : Unsatisfiable (PosFin 65) f7999 := by
  apply lratCheckerSound f7999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7999
  · intro a ha; simp [p7999] at ha; subst a; trivial
  · exact checked7999
theorem derived7999 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7999 := by
  apply localUnsat_implies_entails f7999 [c7997, c1368, c7998, c3616, c3685, c3287, c1277, c420, c3980, c7948, c468] c7999 unsat7999 (by rfl) a
  have h0 : Entails.eval a c7997 := derived7997 a h
  have h1 : Entails.eval a c1368 := h 1367 (by decide)
  have h2 : Entails.eval a c7998 := derived7998 a h
  have h3 : Entails.eval a c3616 := h 3615 (by decide)
  have h4 : Entails.eval a c3685 := h 3684 (by decide)
  have h5 : Entails.eval a c3287 := h 3286 (by decide)
  have h6 : Entails.eval a c1277 := h 1276 (by decide)
  have h7 : Entails.eval a c420 := h 419 (by decide)
  have h8 : Entails.eval a c3980 := h 3979 (by decide)
  have h9 : Entails.eval a c7948 := derived7948 a h
  have h10 : Entails.eval a c468 := h 467 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8000 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8000 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7999, some c7987, some c1941, some c2061, some c4340, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8000 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8000 : lratChecker f8000 p8000 = .success := by decide +kernel
theorem unsat8000 : Unsatisfiable (PosFin 65) f8000 := by
  apply lratCheckerSound f8000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8000
  · intro a ha; simp [p8000] at ha; subst a; trivial
  · exact checked8000
theorem derived8000 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8000 := by
  apply localUnsat_implies_entails f8000 [c7999, c7987, c1941, c2061, c4340] c8000 unsat8000 (by rfl) a
  have h0 : Entails.eval a c7999 := derived7999 a h
  have h1 : Entails.eval a c7987 := derived7987 a h
  have h2 : Entails.eval a c1941 := h 1940 (by decide)
  have h3 : Entails.eval a c2061 := h 2060 (by decide)
  have h4 : Entails.eval a c4340 := h 4339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8001 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8001 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7999, some c8000, some c3647, some c3685, some c2320, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p8001 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8001 : lratChecker f8001 p8001 = .success := by decide +kernel
theorem unsat8001 : Unsatisfiable (PosFin 65) f8001 := by
  apply lratCheckerSound f8001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8001
  · intro a ha; simp [p8001] at ha; subst a; trivial
  · exact checked8001
theorem derived8001 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8001 := by
  apply localUnsat_implies_entails f8001 [c7999, c8000, c3647, c3685, c2320] c8001 unsat8001 (by rfl) a
  have h0 : Entails.eval a c7999 := derived7999 a h
  have h1 : Entails.eval a c8000 := derived8000 a h
  have h2 : Entails.eval a c3647 := h 3646 (by decide)
  have h3 : Entails.eval a c3685 := h 3684 (by decide)
  have h4 : Entails.eval a c2320 := h 2319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8002 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8002 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8001, some c7982, some c7997, some c2005, some c2320, some c4828, some c3507, some c3768, some c7983, some c2951, some c476, some c486, some c468, some c3831, some c5069, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8002 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8002 : lratChecker f8002 p8002 = .success := by decide +kernel
theorem unsat8002 : Unsatisfiable (PosFin 65) f8002 := by
  apply lratCheckerSound f8002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8002
  · intro a ha; simp [p8002] at ha; subst a; trivial
  · exact checked8002
theorem derived8002 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8002 := by
  apply localUnsat_implies_entails f8002 [c8001, c7982, c7997, c2005, c2320, c4828, c3507, c3768, c7983, c2951, c476, c486, c468, c3831, c5069] c8002 unsat8002 (by rfl) a
  have h0 : Entails.eval a c8001 := derived8001 a h
  have h1 : Entails.eval a c7982 := derived7982 a h
  have h2 : Entails.eval a c7997 := derived7997 a h
  have h3 : Entails.eval a c2005 := h 2004 (by decide)
  have h4 : Entails.eval a c2320 := h 2319 (by decide)
  have h5 : Entails.eval a c4828 := h 4827 (by decide)
  have h6 : Entails.eval a c3507 := h 3506 (by decide)
  have h7 : Entails.eval a c3768 := h 3767 (by decide)
  have h8 : Entails.eval a c7983 := derived7983 a h
  have h9 : Entails.eval a c2951 := h 2950 (by decide)
  have h10 : Entails.eval a c476 := h 475 (by decide)
  have h11 : Entails.eval a c486 := h 485 (by decide)
  have h12 : Entails.eval a c468 := h 467 (by decide)
  have h13 : Entails.eval a c3831 := h 3830 (by decide)
  have h14 : Entails.eval a c5069 := h 5068 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8003 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8003 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8001, some c7982, some c8002, some c4954, some c5124, some c2061, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8003 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8003 : lratChecker f8003 p8003 = .success := by decide +kernel
theorem unsat8003 : Unsatisfiable (PosFin 65) f8003 := by
  apply lratCheckerSound f8003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8003
  · intro a ha; simp [p8003] at ha; subst a; trivial
  · exact checked8003
theorem derived8003 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8003 := by
  apply localUnsat_implies_entails f8003 [c8001, c7982, c8002, c4954, c5124, c2061] c8003 unsat8003 (by rfl) a
  have h0 : Entails.eval a c8001 := derived8001 a h
  have h1 : Entails.eval a c7982 := derived7982 a h
  have h2 : Entails.eval a c8002 := derived8002 a h
  have h3 : Entails.eval a c4954 := h 4953 (by decide)
  have h4 : Entails.eval a c5124 := h 5123 (by decide)
  have h5 : Entails.eval a c2061 := h 2060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8004 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8004 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7997, some c7952, some c7948, some c6318, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8004 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8004 : lratChecker f8004 p8004 = .success := by decide +kernel
theorem unsat8004 : Unsatisfiable (PosFin 65) f8004 := by
  apply lratCheckerSound f8004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8004
  · intro a ha; simp [p8004] at ha; subst a; trivial
  · exact checked8004
theorem derived8004 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8004 := by
  apply localUnsat_implies_entails f8004 [c7997, c7952, c7948, c6318] c8004 unsat8004 (by rfl) a
  have h0 : Entails.eval a c7997 := derived7997 a h
  have h1 : Entails.eval a c7952 := derived7952 a h
  have h2 : Entails.eval a c7948 := derived7948 a h
  have h3 : Entails.eval a c6318 := h 6317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8005 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8005 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8001, some c7982, some c8003, some c2167, some c1277, some c3287, some c7997, some c6318, some c6942, some c549, some c6477, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8005 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8005 : lratChecker f8005 p8005 = .success := by decide +kernel
theorem unsat8005 : Unsatisfiable (PosFin 65) f8005 := by
  apply lratCheckerSound f8005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8005
  · intro a ha; simp [p8005] at ha; subst a; trivial
  · exact checked8005
theorem derived8005 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8005 := by
  apply localUnsat_implies_entails f8005 [c8001, c7982, c8003, c2167, c1277, c3287, c7997, c6318, c6942, c549, c6477] c8005 unsat8005 (by rfl) a
  have h0 : Entails.eval a c8001 := derived8001 a h
  have h1 : Entails.eval a c7982 := derived7982 a h
  have h2 : Entails.eval a c8003 := derived8003 a h
  have h3 : Entails.eval a c2167 := h 2166 (by decide)
  have h4 : Entails.eval a c1277 := h 1276 (by decide)
  have h5 : Entails.eval a c3287 := h 3286 (by decide)
  have h6 : Entails.eval a c7997 := derived7997 a h
  have h7 : Entails.eval a c6318 := h 6317 (by decide)
  have h8 : Entails.eval a c6942 := h 6941 (by decide)
  have h9 : Entails.eval a c549 := h 548 (by decide)
  have h10 : Entails.eval a c6477 := h 6476 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8006 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8006 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8005, some c8004, some c8001, some c7982, some c8003, some c2167, some c1277, some c3287, some c7998, some c7997, some c7946, some c7342, some c6406, some c551, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8006 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8006 : lratChecker f8006 p8006 = .success := by decide +kernel
theorem unsat8006 : Unsatisfiable (PosFin 65) f8006 := by
  apply lratCheckerSound f8006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8006
  · intro a ha; simp [p8006] at ha; subst a; trivial
  · exact checked8006
theorem derived8006 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8006 := by
  apply localUnsat_implies_entails f8006 [c8005, c8004, c8001, c7982, c8003, c2167, c1277, c3287, c7998, c7997, c7946, c7342, c6406, c551] c8006 unsat8006 (by rfl) a
  have h0 : Entails.eval a c8005 := derived8005 a h
  have h1 : Entails.eval a c8004 := derived8004 a h
  have h2 : Entails.eval a c8001 := derived8001 a h
  have h3 : Entails.eval a c7982 := derived7982 a h
  have h4 : Entails.eval a c8003 := derived8003 a h
  have h5 : Entails.eval a c2167 := h 2166 (by decide)
  have h6 : Entails.eval a c1277 := h 1276 (by decide)
  have h7 : Entails.eval a c3287 := h 3286 (by decide)
  have h8 : Entails.eval a c7998 := derived7998 a h
  have h9 : Entails.eval a c7997 := derived7997 a h
  have h10 : Entails.eval a c7946 := derived7946 a h
  have h11 : Entails.eval a c7342 := h 7341 (by decide)
  have h12 : Entails.eval a c6406 := h 6405 (by decide)
  have h13 : Entails.eval a c551 := h 550 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8007 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8007 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7997, some c8001, some c7982, some c8003, some c1277, some c3011, some c8004, some c8005, some c8006, some c440, some c7957, some c7384, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8007 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8007 : lratChecker f8007 p8007 = .success := by decide +kernel
theorem unsat8007 : Unsatisfiable (PosFin 65) f8007 := by
  apply lratCheckerSound f8007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8007
  · intro a ha; simp [p8007] at ha; subst a; trivial
  · exact checked8007
theorem derived8007 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8007 := by
  apply localUnsat_implies_entails f8007 [c7997, c8001, c7982, c8003, c1277, c3011, c8004, c8005, c8006, c440, c7957, c7384] c8007 unsat8007 (by rfl) a
  have h0 : Entails.eval a c7997 := derived7997 a h
  have h1 : Entails.eval a c8001 := derived8001 a h
  have h2 : Entails.eval a c7982 := derived7982 a h
  have h3 : Entails.eval a c8003 := derived8003 a h
  have h4 : Entails.eval a c1277 := h 1276 (by decide)
  have h5 : Entails.eval a c3011 := h 3010 (by decide)
  have h6 : Entails.eval a c8004 := derived8004 a h
  have h7 : Entails.eval a c8005 := derived8005 a h
  have h8 : Entails.eval a c8006 := derived8006 a h
  have h9 : Entails.eval a c440 := h 439 (by decide)
  have h10 : Entails.eval a c7957 := derived7957 a h
  have h11 : Entails.eval a c7384 := h 7383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8008 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨39, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨44, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8008 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c7383, some c7389, some c2941, some c2415, some c2633, some c2634, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8008 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8008 : lratChecker f8008 p8008 = .success := by decide +kernel
theorem unsat8008 : Unsatisfiable (PosFin 65) f8008 := by
  apply lratCheckerSound f8008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8008
  · intro a ha; simp [p8008] at ha; subst a; trivial
  · exact checked8008
theorem derived8008 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8008 := by
  apply localUnsat_implies_entails f8008 [c8007, c7383, c7389, c2941, c2415, c2633, c2634] c8008 unsat8008 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c7383 := h 7382 (by decide)
  have h2 : Entails.eval a c7389 := h 7388 (by decide)
  have h3 : Entails.eval a c2941 := h 2940 (by decide)
  have h4 : Entails.eval a c2415 := h 2414 (by decide)
  have h5 : Entails.eval a c2633 := h 2632 (by decide)
  have h6 : Entails.eval a c2634 := h 2633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8009 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8009 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c439, some c442, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8009 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8009 : lratChecker f8009 p8009 = .success := by decide +kernel
theorem unsat8009 : Unsatisfiable (PosFin 65) f8009 := by
  apply lratCheckerSound f8009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8009
  · intro a ha; simp [p8009] at ha; subst a; trivial
  · exact checked8009
theorem derived8009 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8009 := by
  apply localUnsat_implies_entails f8009 [c8007, c439, c442] c8009 unsat8009 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c439 := h 438 (by decide)
  have h2 : Entails.eval a c442 := h 441 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8010 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8010 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1169, some c2180, some c2498, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8010 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8010 : lratChecker f8010 p8010 = .success := by decide +kernel
theorem unsat8010 : Unsatisfiable (PosFin 65) f8010 := by
  apply lratCheckerSound f8010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8010
  · intro a ha; simp [p8010] at ha; subst a; trivial
  · exact checked8010
theorem derived8010 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8010 := by
  apply localUnsat_implies_entails f8010 [c1169, c2180, c2498] c8010 unsat8010 (by rfl) a
  have h0 : Entails.eval a c1169 := h 1168 (by decide)
  have h1 : Entails.eval a c2180 := h 2179 (by decide)
  have h2 : Entails.eval a c2498 := h 2497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8011 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8011 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8010, some c2947, some c4, some c7770, some c63, some c7340, some c2165, some c8009, some c8008, some c7063, some c3872, some c4190, some c4222, some c5122, some c5070, some c2908, some c1139, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8011 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8011 : lratChecker f8011 p8011 = .success := by decide +kernel
theorem unsat8011 : Unsatisfiable (PosFin 65) f8011 := by
  apply lratCheckerSound f8011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8011
  · intro a ha; simp [p8011] at ha; subst a; trivial
  · exact checked8011
theorem derived8011 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8011 := by
  apply localUnsat_implies_entails f8011 [c8007, c8010, c2947, c4, c7770, c63, c7340, c2165, c8009, c8008, c7063, c3872, c4190, c4222, c5122, c5070, c2908, c1139] c8011 unsat8011 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8010 := derived8010 a h
  have h2 : Entails.eval a c2947 := h 2946 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c7770 := derived7770 a h
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c7340 := h 7339 (by decide)
  have h7 : Entails.eval a c2165 := h 2164 (by decide)
  have h8 : Entails.eval a c8009 := derived8009 a h
  have h9 : Entails.eval a c8008 := derived8008 a h
  have h10 : Entails.eval a c7063 := h 7062 (by decide)
  have h11 : Entails.eval a c3872 := h 3871 (by decide)
  have h12 : Entails.eval a c4190 := h 4189 (by decide)
  have h13 : Entails.eval a c4222 := h 4221 (by decide)
  have h14 : Entails.eval a c5122 := h 5121 (by decide)
  have h15 : Entails.eval a c5070 := h 5069 (by decide)
  have h16 : Entails.eval a c2908 := h 2907 (by decide)
  have h17 : Entails.eval a c1139 := h 1138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8012 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8012 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8010, some c8011, some c3007, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8012 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8012 : lratChecker f8012 p8012 = .success := by decide +kernel
theorem unsat8012 : Unsatisfiable (PosFin 65) f8012 := by
  apply lratCheckerSound f8012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8012
  · intro a ha; simp [p8012] at ha; subst a; trivial
  · exact checked8012
theorem derived8012 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8012 := by
  apply localUnsat_implies_entails f8012 [c8007, c8010, c8011, c3007] c8012 unsat8012 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8010 := derived8010 a h
  have h2 : Entails.eval a c8011 := derived8011 a h
  have h3 : Entails.eval a c3007 := h 3006 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8013 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8013 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c1302, some c1273, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8013 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8013 : lratChecker f8013 p8013 = .success := by decide +kernel
theorem unsat8013 : Unsatisfiable (PosFin 65) f8013 := by
  apply lratCheckerSound f8013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8013
  · intro a ha; simp [p8013] at ha; subst a; trivial
  · exact checked8013
theorem derived8013 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8013 := by
  apply localUnsat_implies_entails f8013 [c8007, c1302, c1273] c8013 unsat8013 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c1302 := h 1301 (by decide)
  have h2 : Entails.eval a c1273 := h 1272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8014 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8014 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8013, some c8010, some c8012, some c2165, some c3378, some c3286, some c3682, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8014 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8014 : lratChecker f8014 p8014 = .success := by decide +kernel
theorem unsat8014 : Unsatisfiable (PosFin 65) f8014 := by
  apply lratCheckerSound f8014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8014
  · intro a ha; simp [p8014] at ha; subst a; trivial
  · exact checked8014
theorem derived8014 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8014 := by
  apply localUnsat_implies_entails f8014 [c8007, c8013, c8010, c8012, c2165, c3378, c3286, c3682] c8014 unsat8014 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8013 := derived8013 a h
  have h2 : Entails.eval a c8010 := derived8010 a h
  have h3 : Entails.eval a c8012 := derived8012 a h
  have h4 : Entails.eval a c2165 := h 2164 (by decide)
  have h5 : Entails.eval a c3378 := h 3377 (by decide)
  have h6 : Entails.eval a c3286 := h 3285 (by decide)
  have h7 : Entails.eval a c3682 := h 3681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8015 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8015 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3378, some c3286, some c3682, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8015 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8015 : lratChecker f8015 p8015 = .success := by decide +kernel
theorem unsat8015 : Unsatisfiable (PosFin 65) f8015 := by
  apply lratCheckerSound f8015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8015
  · intro a ha; simp [p8015] at ha; subst a; trivial
  · exact checked8015
theorem derived8015 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8015 := by
  apply localUnsat_implies_entails f8015 [c3378, c3286, c3682] c8015 unsat8015 (by rfl) a
  have h0 : Entails.eval a c3378 := h 3377 (by decide)
  have h1 : Entails.eval a c3286 := h 3285 (by decide)
  have h2 : Entails.eval a c3682 := h 3681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8016 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨55, by decide⟩, true), (⟨1, by decide⟩, true), (⟨12, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8016 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5081, some c5097, some c2237, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8016 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8016 : lratChecker f8016 p8016 = .success := by decide +kernel
theorem unsat8016 : Unsatisfiable (PosFin 65) f8016 := by
  apply lratCheckerSound f8016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8016
  · intro a ha; simp [p8016] at ha; subst a; trivial
  · exact checked8016
theorem derived8016 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8016 := by
  apply localUnsat_implies_entails f8016 [c5081, c5097, c2237] c8016 unsat8016 (by rfl) a
  have h0 : Entails.eval a c5081 := h 5080 (by decide)
  have h1 : Entails.eval a c5097 := h 5096 (by decide)
  have h2 : Entails.eval a c2237 := h 2236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8017 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨12, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8017 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8016, some c3378, some c3286, some c5003, some c4953, some c2237, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8017 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8017 : lratChecker f8017 p8017 = .success := by decide +kernel
theorem unsat8017 : Unsatisfiable (PosFin 65) f8017 := by
  apply lratCheckerSound f8017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8017
  · intro a ha; simp [p8017] at ha; subst a; trivial
  · exact checked8017
theorem derived8017 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8017 := by
  apply localUnsat_implies_entails f8017 [c8016, c3378, c3286, c5003, c4953, c2237] c8017 unsat8017 (by rfl) a
  have h0 : Entails.eval a c8016 := derived8016 a h
  have h1 : Entails.eval a c3378 := h 3377 (by decide)
  have h2 : Entails.eval a c3286 := h 3285 (by decide)
  have h3 : Entails.eval a c5003 := h 5002 (by decide)
  have h4 : Entails.eval a c4953 := h 4952 (by decide)
  have h5 : Entails.eval a c2237 := h 2236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8018 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨12, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8018 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3293, some c2498, some c2760, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8018 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8018 : lratChecker f8018 p8018 = .success := by decide +kernel
theorem unsat8018 : Unsatisfiable (PosFin 65) f8018 := by
  apply lratCheckerSound f8018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8018
  · intro a ha; simp [p8018] at ha; subst a; trivial
  · exact checked8018
theorem derived8018 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8018 := by
  apply localUnsat_implies_entails f8018 [c3293, c2498, c2760] c8018 unsat8018 (by rfl) a
  have h0 : Entails.eval a c3293 := h 3292 (by decide)
  have h1 : Entails.eval a c2498 := h 2497 (by decide)
  have h2 : Entails.eval a c2760 := h 2759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8019 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨12, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8019 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8017, some c8018, some c5088, some c3355, some c2521, some c4399, some c2760, some c1753, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8019 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8019 : lratChecker f8019 p8019 = .success := by decide +kernel
theorem unsat8019 : Unsatisfiable (PosFin 65) f8019 := by
  apply lratCheckerSound f8019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8019
  · intro a ha; simp [p8019] at ha; subst a; trivial
  · exact checked8019
theorem derived8019 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8019 := by
  apply localUnsat_implies_entails f8019 [c8007, c8017, c8018, c5088, c3355, c2521, c4399, c2760, c1753] c8019 unsat8019 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8017 := derived8017 a h
  have h2 : Entails.eval a c8018 := derived8018 a h
  have h3 : Entails.eval a c5088 := h 5087 (by decide)
  have h4 : Entails.eval a c3355 := h 3354 (by decide)
  have h5 : Entails.eval a c2521 := h 2520 (by decide)
  have h6 : Entails.eval a c4399 := h 4398 (by decide)
  have h7 : Entails.eval a c2760 := h 2759 (by decide)
  have h8 : Entails.eval a c1753 := h 1752 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8020 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨12, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8020 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c473, some c3441, some c1587, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8020 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8020 : lratChecker f8020 p8020 = .success := by decide +kernel
theorem unsat8020 : Unsatisfiable (PosFin 65) f8020 := by
  apply lratCheckerSound f8020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8020
  · intro a ha; simp [p8020] at ha; subst a; trivial
  · exact checked8020
theorem derived8020 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8020 := by
  apply localUnsat_implies_entails f8020 [c473, c3441, c1587] c8020 unsat8020 (by rfl) a
  have h0 : Entails.eval a c473 := h 472 (by decide)
  have h1 : Entails.eval a c3441 := h 3440 (by decide)
  have h2 : Entails.eval a c1587 := h 1586 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8021 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8021 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8014, some c8019, some c8020, some c3422, some c3436, some c2353, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8021 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8021 : lratChecker f8021 p8021 = .success := by decide +kernel
theorem unsat8021 : Unsatisfiable (PosFin 65) f8021 := by
  apply lratCheckerSound f8021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8021
  · intro a ha; simp [p8021] at ha; subst a; trivial
  · exact checked8021
theorem derived8021 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8021 := by
  apply localUnsat_implies_entails f8021 [c8007, c8014, c8019, c8020, c3422, c3436, c2353] c8021 unsat8021 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8014 := derived8014 a h
  have h2 : Entails.eval a c8019 := derived8019 a h
  have h3 : Entails.eval a c8020 := derived8020 a h
  have h4 : Entails.eval a c3422 := h 3421 (by decide)
  have h5 : Entails.eval a c3436 := h 3435 (by decide)
  have h6 : Entails.eval a c2353 := h 2352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8022 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8022 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c418, some c35, some c467, some c4257, some c3477, some c1564, some c3682, some c490, some c1726, some c7822, some c4516, some c49, some c2237, some c5704, some c5730, some c1060, some c1061, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8022 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8022 : lratChecker f8022 p8022 = .success := by decide +kernel
theorem unsat8022 : Unsatisfiable (PosFin 65) f8022 := by
  apply lratCheckerSound f8022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8022
  · intro a ha; simp [p8022] at ha; subst a; trivial
  · exact checked8022
theorem derived8022 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8022 := by
  apply localUnsat_implies_entails f8022 [c8007, c418, c35, c467, c4257, c3477, c1564, c3682, c490, c1726, c7822, c4516, c49, c2237, c5704, c5730, c1060, c1061] c8022 unsat8022 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c418 := h 417 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c467 := h 466 (by decide)
  have h4 : Entails.eval a c4257 := h 4256 (by decide)
  have h5 : Entails.eval a c3477 := h 3476 (by decide)
  have h6 : Entails.eval a c1564 := h 1563 (by decide)
  have h7 : Entails.eval a c3682 := h 3681 (by decide)
  have h8 : Entails.eval a c490 := h 489 (by decide)
  have h9 : Entails.eval a c1726 := h 1725 (by decide)
  have h10 : Entails.eval a c7822 := derived7822 a h
  have h11 : Entails.eval a c4516 := h 4515 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c2237 := h 2236 (by decide)
  have h14 : Entails.eval a c5704 := h 5703 (by decide)
  have h15 : Entails.eval a c5730 := h 5729 (by decide)
  have h16 : Entails.eval a c1060 := h 1059 (by decide)
  have h17 : Entails.eval a c1061 := h 1060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8023 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8023 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8021, some c8007, some c8022, some c6808, some c425, some c473, some c42, some c7316, some c3488, some c1587, some c7127, some c3412, some c7069, some c4470, some c54, some c69, some c5713, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8023 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8023 : lratChecker f8023 p8023 = .success := by decide +kernel
theorem unsat8023 : Unsatisfiable (PosFin 65) f8023 := by
  apply lratCheckerSound f8023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8023
  · intro a ha; simp [p8023] at ha; subst a; trivial
  · exact checked8023
theorem derived8023 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8023 := by
  apply localUnsat_implies_entails f8023 [c8021, c8007, c8022, c6808, c425, c473, c42, c7316, c3488, c1587, c7127, c3412, c7069, c4470, c54, c69, c5713] c8023 unsat8023 (by rfl) a
  have h0 : Entails.eval a c8021 := derived8021 a h
  have h1 : Entails.eval a c8007 := derived8007 a h
  have h2 : Entails.eval a c8022 := derived8022 a h
  have h3 : Entails.eval a c6808 := h 6807 (by decide)
  have h4 : Entails.eval a c425 := h 424 (by decide)
  have h5 : Entails.eval a c473 := h 472 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c7316 := h 7315 (by decide)
  have h8 : Entails.eval a c3488 := h 3487 (by decide)
  have h9 : Entails.eval a c1587 := h 1586 (by decide)
  have h10 : Entails.eval a c7127 := h 7126 (by decide)
  have h11 : Entails.eval a c3412 := h 3411 (by decide)
  have h12 : Entails.eval a c7069 := h 7068 (by decide)
  have h13 : Entails.eval a c4470 := h 4469 (by decide)
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c5713 := h 5712 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8024 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8024 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1753, some c3293, some c3267, some c4399, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8024 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8024 : lratChecker f8024 p8024 = .success := by decide +kernel
theorem unsat8024 : Unsatisfiable (PosFin 65) f8024 := by
  apply lratCheckerSound f8024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8024
  · intro a ha; simp [p8024] at ha; subst a; trivial
  · exact checked8024
theorem derived8024 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8024 := by
  apply localUnsat_implies_entails f8024 [c1753, c3293, c3267, c4399] c8024 unsat8024 (by rfl) a
  have h0 : Entails.eval a c1753 := h 1752 (by decide)
  have h1 : Entails.eval a c3293 := h 3292 (by decide)
  have h2 : Entails.eval a c3267 := h 3266 (by decide)
  have h3 : Entails.eval a c4399 := h 4398 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8025 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8025 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c460, some c526, some c506, some c2537, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8025 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8025 : lratChecker f8025 p8025 = .success := by decide +kernel
theorem unsat8025 : Unsatisfiable (PosFin 65) f8025 := by
  apply lratCheckerSound f8025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8025
  · intro a ha; simp [p8025] at ha; subst a; trivial
  · exact checked8025
theorem derived8025 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8025 := by
  apply localUnsat_implies_entails f8025 [c460, c526, c506, c2537] c8025 unsat8025 (by rfl) a
  have h0 : Entails.eval a c460 := h 459 (by decide)
  have h1 : Entails.eval a c526 := h 525 (by decide)
  have h2 : Entails.eval a c506 := h 505 (by decide)
  have h3 : Entails.eval a c2537 := h 2536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8026 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8026 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6808, some c7316, some c7127, some c7069, some c6338, some c7774, some c6724, some c8025, some c3293, some c3267, some c8024, some c2106, some c2109, some c2096, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8026 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8026 : lratChecker f8026 p8026 = .success := by decide +kernel
theorem unsat8026 : Unsatisfiable (PosFin 65) f8026 := by
  apply lratCheckerSound f8026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8026
  · intro a ha; simp [p8026] at ha; subst a; trivial
  · exact checked8026
theorem derived8026 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8026 := by
  apply localUnsat_implies_entails f8026 [c6808, c7316, c7127, c7069, c6338, c7774, c6724, c8025, c3293, c3267, c8024, c2106, c2109, c2096] c8026 unsat8026 (by rfl) a
  have h0 : Entails.eval a c6808 := h 6807 (by decide)
  have h1 : Entails.eval a c7316 := h 7315 (by decide)
  have h2 : Entails.eval a c7127 := h 7126 (by decide)
  have h3 : Entails.eval a c7069 := h 7068 (by decide)
  have h4 : Entails.eval a c6338 := h 6337 (by decide)
  have h5 : Entails.eval a c7774 := derived7774 a h
  have h6 : Entails.eval a c6724 := h 6723 (by decide)
  have h7 : Entails.eval a c8025 := derived8025 a h
  have h8 : Entails.eval a c3293 := h 3292 (by decide)
  have h9 : Entails.eval a c3267 := h 3266 (by decide)
  have h10 : Entails.eval a c8024 := derived8024 a h
  have h11 : Entails.eval a c2106 := h 2105 (by decide)
  have h12 : Entails.eval a c2109 := h 2108 (by decide)
  have h13 : Entails.eval a c2096 := h 2095 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8027 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8027 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3727, some c2947, some c3477, some c3872, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8027 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8027 : lratChecker f8027 p8027 = .success := by decide +kernel
theorem unsat8027 : Unsatisfiable (PosFin 65) f8027 := by
  apply lratCheckerSound f8027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8027
  · intro a ha; simp [p8027] at ha; subst a; trivial
  · exact checked8027
theorem derived8027 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8027 := by
  apply localUnsat_implies_entails f8027 [c3727, c2947, c3477, c3872] c8027 unsat8027 (by rfl) a
  have h0 : Entails.eval a c3727 := h 3726 (by decide)
  have h1 : Entails.eval a c2947 := h 2946 (by decide)
  have h2 : Entails.eval a c3477 := h 3476 (by decide)
  have h3 : Entails.eval a c3872 := h 3871 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8028 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8028 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8015, some c1363, some c3792, some c3340, some c2237, some c5030, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p8028 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8028 : lratChecker f8028 p8028 = .success := by decide +kernel
theorem unsat8028 : Unsatisfiable (PosFin 65) f8028 := by
  apply lratCheckerSound f8028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8028
  · intro a ha; simp [p8028] at ha; subst a; trivial
  · exact checked8028
theorem derived8028 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8028 := by
  apply localUnsat_implies_entails f8028 [c8015, c1363, c3792, c3340, c2237, c5030] c8028 unsat8028 (by rfl) a
  have h0 : Entails.eval a c8015 := derived8015 a h
  have h1 : Entails.eval a c1363 := h 1362 (by decide)
  have h2 : Entails.eval a c3792 := h 3791 (by decide)
  have h3 : Entails.eval a c3340 := h 3339 (by decide)
  have h4 : Entails.eval a c2237 := h 2236 (by decide)
  have h5 : Entails.eval a c5030 := h 5029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8029 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8029 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8027, some c8028, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p8029 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8029 : lratChecker f8029 p8029 = .success := by decide +kernel
theorem unsat8029 : Unsatisfiable (PosFin 65) f8029 := by
  apply lratCheckerSound f8029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8029
  · intro a ha; simp [p8029] at ha; subst a; trivial
  · exact checked8029
theorem derived8029 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8029 := by
  apply localUnsat_implies_entails f8029 [c8027, c8028] c8029 unsat8029 (by rfl) a
  have h0 : Entails.eval a c8027 := derived8027 a h
  have h1 : Entails.eval a c8028 := derived8028 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8030 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8030 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8021, some c8023, some c8026, some c8029, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8030 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8030 : lratChecker f8030 p8030 = .success := by decide +kernel
theorem unsat8030 : Unsatisfiable (PosFin 65) f8030 := by
  apply lratCheckerSound f8030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8030
  · intro a ha; simp [p8030] at ha; subst a; trivial
  · exact checked8030
theorem derived8030 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8030 := by
  apply localUnsat_implies_entails f8030 [c8007, c8021, c8023, c8026, c8029] c8030 unsat8030 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8021 := derived8021 a h
  have h2 : Entails.eval a c8023 := derived8023 a h
  have h3 : Entails.eval a c8026 := derived8026 a h
  have h4 : Entails.eval a c8029 := derived8029 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8031 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8031 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8014, some c8019, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8031 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8031 : lratChecker f8031 p8031 = .success := by decide +kernel
theorem unsat8031 : Unsatisfiable (PosFin 65) f8031 := by
  apply lratCheckerSound f8031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8031
  · intro a ha; simp [p8031] at ha; subst a; trivial
  · exact checked8031
theorem derived8031 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8031 := by
  apply localUnsat_implies_entails f8031 [c8014, c8019] c8031 unsat8031 (by rfl) a
  have h0 : Entails.eval a c8014 := derived8014 a h
  have h1 : Entails.eval a c8019 := derived8019 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8032 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8032 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6966, some c6310, some c6338, some c7316, some c6724, some c7223, some c6664, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8032 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8032 : lratChecker f8032 p8032 = .success := by decide +kernel
theorem unsat8032 : Unsatisfiable (PosFin 65) f8032 := by
  apply lratCheckerSound f8032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8032
  · intro a ha; simp [p8032] at ha; subst a; trivial
  · exact checked8032
theorem derived8032 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8032 := by
  apply localUnsat_implies_entails f8032 [c6966, c6310, c6338, c7316, c6724, c7223, c6664] c8032 unsat8032 (by rfl) a
  have h0 : Entails.eval a c6966 := h 6965 (by decide)
  have h1 : Entails.eval a c6310 := h 6309 (by decide)
  have h2 : Entails.eval a c6338 := h 6337 (by decide)
  have h3 : Entails.eval a c7316 := h 7315 (by decide)
  have h4 : Entails.eval a c6724 := h 6723 (by decide)
  have h5 : Entails.eval a c7223 := h 7222 (by decide)
  have h6 : Entails.eval a c6664 := h 6663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8033 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8033 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8031, some c8029, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8033 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8033 : lratChecker f8033 p8033 = .success := by decide +kernel
theorem unsat8033 : Unsatisfiable (PosFin 65) f8033 := by
  apply lratCheckerSound f8033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8033
  · intro a ha; simp [p8033] at ha; subst a; trivial
  · exact checked8033
theorem derived8033 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8033 := by
  apply localUnsat_implies_entails f8033 [c8031, c8029] c8033 unsat8033 (by rfl) a
  have h0 : Entails.eval a c8031 := derived8031 a h
  have h1 : Entails.eval a c8029 := derived8029 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8034 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨1, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8034 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2060, some c1564, some c2353, some c4081, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8034 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8034 : lratChecker f8034 p8034 = .success := by decide +kernel
theorem unsat8034 : Unsatisfiable (PosFin 65) f8034 := by
  apply lratCheckerSound f8034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8034
  · intro a ha; simp [p8034] at ha; subst a; trivial
  · exact checked8034
theorem derived8034 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8034 := by
  apply localUnsat_implies_entails f8034 [c2060, c1564, c2353, c4081] c8034 unsat8034 (by rfl) a
  have h0 : Entails.eval a c2060 := h 2059 (by decide)
  have h1 : Entails.eval a c1564 := h 1563 (by decide)
  have h2 : Entails.eval a c2353 := h 2352 (by decide)
  have h3 : Entails.eval a c4081 := h 4080 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8035 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8035 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8030, some c8032, some c7250, some c6959, some c7044, some c6329, some c7473, some c8033, some c418, some c490, some c8034, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8035 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8035 : lratChecker f8035 p8035 = .success := by decide +kernel
theorem unsat8035 : Unsatisfiable (PosFin 65) f8035 := by
  apply lratCheckerSound f8035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8035
  · intro a ha; simp [p8035] at ha; subst a; trivial
  · exact checked8035
theorem derived8035 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8035 := by
  apply localUnsat_implies_entails f8035 [c8007, c8030, c8032, c7250, c6959, c7044, c6329, c7473, c8033, c418, c490, c8034] c8035 unsat8035 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8030 := derived8030 a h
  have h2 : Entails.eval a c8032 := derived8032 a h
  have h3 : Entails.eval a c7250 := h 7249 (by decide)
  have h4 : Entails.eval a c6959 := h 6958 (by decide)
  have h5 : Entails.eval a c7044 := h 7043 (by decide)
  have h6 : Entails.eval a c6329 := h 6328 (by decide)
  have h7 : Entails.eval a c7473 := h 7472 (by decide)
  have h8 : Entails.eval a c8033 := derived8033 a h
  have h9 : Entails.eval a c418 := h 417 (by decide)
  have h10 : Entails.eval a c490 := h 489 (by decide)
  have h11 : Entails.eval a c8034 := derived8034 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8036 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8036 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6547, some c6815, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8036 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8036 : lratChecker f8036 p8036 = .success := by decide +kernel
theorem unsat8036 : Unsatisfiable (PosFin 65) f8036 := by
  apply lratCheckerSound f8036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8036
  · intro a ha; simp [p8036] at ha; subst a; trivial
  · exact checked8036
theorem derived8036 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8036 := by
  apply localUnsat_implies_entails f8036 [c6371, c6547, c6815] c8036 unsat8036 (by rfl) a
  have h0 : Entails.eval a c6371 := h 6370 (by decide)
  have h1 : Entails.eval a c6547 := h 6546 (by decide)
  have h2 : Entails.eval a c6815 := h 6814 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8037 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8037 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8034, some c490, some c8029, some c8019, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8037 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8037 : lratChecker f8037 p8037 = .success := by decide +kernel
theorem unsat8037 : Unsatisfiable (PosFin 65) f8037 := by
  apply lratCheckerSound f8037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8037
  · intro a ha; simp [p8037] at ha; subst a; trivial
  · exact checked8037
theorem derived8037 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8037 := by
  apply localUnsat_implies_entails f8037 [c8034, c490, c8029, c8019] c8037 unsat8037 (by rfl) a
  have h0 : Entails.eval a c8034 := derived8034 a h
  have h1 : Entails.eval a c490 := h 489 (by decide)
  have h2 : Entails.eval a c8029 := derived8029 a h
  have h3 : Entails.eval a c8019 := derived8019 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8038 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨55, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8038 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8036, some c490, some c8029, some c8028, some c5122, some c2947, some c3450, some c544, some c558, some c6434, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8038 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8038 : lratChecker f8038 p8038 = .success := by decide +kernel
theorem unsat8038 : Unsatisfiable (PosFin 65) f8038 := by
  apply lratCheckerSound f8038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8038
  · intro a ha; simp [p8038] at ha; subst a; trivial
  · exact checked8038
theorem derived8038 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8038 := by
  apply localUnsat_implies_entails f8038 [c8036, c490, c8029, c8028, c5122, c2947, c3450, c544, c558, c6434] c8038 unsat8038 (by rfl) a
  have h0 : Entails.eval a c8036 := derived8036 a h
  have h1 : Entails.eval a c490 := h 489 (by decide)
  have h2 : Entails.eval a c8029 := derived8029 a h
  have h3 : Entails.eval a c8028 := derived8028 a h
  have h4 : Entails.eval a c5122 := h 5121 (by decide)
  have h5 : Entails.eval a c2947 := h 2946 (by decide)
  have h6 : Entails.eval a c3450 := h 3449 (by decide)
  have h7 : Entails.eval a c544 := h 543 (by decide)
  have h8 : Entails.eval a c558 := h 557 (by decide)
  have h9 : Entails.eval a c6434 := h 6433 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8039 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8039 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8029, some c8028, some c2165, some c3007, some c3839, some c3378, some c5070, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8039 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8039 : lratChecker f8039 p8039 = .success := by decide +kernel
theorem unsat8039 : Unsatisfiable (PosFin 65) f8039 := by
  apply lratCheckerSound f8039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8039
  · intro a ha; simp [p8039] at ha; subst a; trivial
  · exact checked8039
theorem derived8039 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8039 := by
  apply localUnsat_implies_entails f8039 [c8029, c8028, c2165, c3007, c3839, c3378, c5070] c8039 unsat8039 (by rfl) a
  have h0 : Entails.eval a c8029 := derived8029 a h
  have h1 : Entails.eval a c8028 := derived8028 a h
  have h2 : Entails.eval a c2165 := h 2164 (by decide)
  have h3 : Entails.eval a c3007 := h 3006 (by decide)
  have h4 : Entails.eval a c3839 := h 3838 (by decide)
  have h5 : Entails.eval a c3378 := h 3377 (by decide)
  have h6 : Entails.eval a c5070 := h 5069 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8040 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8040 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3727, some c3477, some c3839, some c4157, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8040 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8040 : lratChecker f8040 p8040 = .success := by decide +kernel
theorem unsat8040 : Unsatisfiable (PosFin 65) f8040 := by
  apply lratCheckerSound f8040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8040
  · intro a ha; simp [p8040] at ha; subst a; trivial
  · exact checked8040
theorem derived8040 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8040 := by
  apply localUnsat_implies_entails f8040 [c3727, c3477, c3839, c4157] c8040 unsat8040 (by rfl) a
  have h0 : Entails.eval a c3727 := h 3726 (by decide)
  have h1 : Entails.eval a c3477 := h 3476 (by decide)
  have h2 : Entails.eval a c3839 := h 3838 (by decide)
  have h3 : Entails.eval a c4157 := h 4156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8041 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8041 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8035, some c8036, some c8037, some c8038, some c8039, some c1273, some c35, some c8040, some c1363, some c4936, some c4190, some c3682, some c467, some c4492, some c6388, some c6959, some c7044, some c49, some c6404, some c5704, some c63, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8041 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8041 : lratChecker f8041 p8041 = .success := by decide +kernel
theorem unsat8041 : Unsatisfiable (PosFin 65) f8041 := by
  apply lratCheckerSound f8041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8041
  · intro a ha; simp [p8041] at ha; subst a; trivial
  · exact checked8041
theorem derived8041 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8041 := by
  apply localUnsat_implies_entails f8041 [c8035, c8036, c8037, c8038, c8039, c1273, c35, c8040, c1363, c4936, c4190, c3682, c467, c4492, c6388, c6959, c7044, c49, c6404, c5704, c63] c8041 unsat8041 (by rfl) a
  have h0 : Entails.eval a c8035 := derived8035 a h
  have h1 : Entails.eval a c8036 := derived8036 a h
  have h2 : Entails.eval a c8037 := derived8037 a h
  have h3 : Entails.eval a c8038 := derived8038 a h
  have h4 : Entails.eval a c8039 := derived8039 a h
  have h5 : Entails.eval a c1273 := h 1272 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c8040 := derived8040 a h
  have h8 : Entails.eval a c1363 := h 1362 (by decide)
  have h9 : Entails.eval a c4936 := h 4935 (by decide)
  have h10 : Entails.eval a c4190 := h 4189 (by decide)
  have h11 : Entails.eval a c3682 := h 3681 (by decide)
  have h12 : Entails.eval a c467 := h 466 (by decide)
  have h13 : Entails.eval a c4492 := h 4491 (by decide)
  have h14 : Entails.eval a c6388 := h 6387 (by decide)
  have h15 : Entails.eval a c6959 := h 6958 (by decide)
  have h16 : Entails.eval a c7044 := h 7043 (by decide)
  have h17 : Entails.eval a c49 := h 48 (by decide)
  have h18 : Entails.eval a c6404 := h 6403 (by decide)
  have h19 : Entails.eval a c5704 := h 5703 (by decide)
  have h20 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8042 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8042 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c42, some c1450, some c1393, some c4470, some c4197, some c473, some c6382, some c6966, some c6936, some c54, some c7316, some c5713, some c69, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8042 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8042 : lratChecker f8042 p8042 = .success := by decide +kernel
theorem unsat8042 : Unsatisfiable (PosFin 65) f8042 := by
  apply lratCheckerSound f8042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8042
  · intro a ha; simp [p8042] at ha; subst a; trivial
  · exact checked8042
theorem derived8042 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8042 := by
  apply localUnsat_implies_entails f8042 [c42, c1450, c1393, c4470, c4197, c473, c6382, c6966, c6936, c54, c7316, c5713, c69] c8042 unsat8042 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c1450 := h 1449 (by decide)
  have h2 : Entails.eval a c1393 := h 1392 (by decide)
  have h3 : Entails.eval a c4470 := h 4469 (by decide)
  have h4 : Entails.eval a c4197 := h 4196 (by decide)
  have h5 : Entails.eval a c473 := h 472 (by decide)
  have h6 : Entails.eval a c6382 := h 6381 (by decide)
  have h7 : Entails.eval a c6966 := h 6965 (by decide)
  have h8 : Entails.eval a c6936 := h 6935 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c7316 := h 7315 (by decide)
  have h11 : Entails.eval a c5713 := h 5712 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8043 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8043 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c42, some c8042, some c1587, some c3050, some c473, some c4470, some c6382, some c6966, some c6936, some c54, some c7316, some c5713, some c69, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8043 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8043 : lratChecker f8043 p8043 = .success := by decide +kernel
theorem unsat8043 : Unsatisfiable (PosFin 65) f8043 := by
  apply lratCheckerSound f8043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8043
  · intro a ha; simp [p8043] at ha; subst a; trivial
  · exact checked8043
theorem derived8043 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8043 := by
  apply localUnsat_implies_entails f8043 [c42, c8042, c1587, c3050, c473, c4470, c6382, c6966, c6936, c54, c7316, c5713, c69] c8043 unsat8043 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c8042 := derived8042 a h
  have h2 : Entails.eval a c1587 := h 1586 (by decide)
  have h3 : Entails.eval a c3050 := h 3049 (by decide)
  have h4 : Entails.eval a c473 := h 472 (by decide)
  have h5 : Entails.eval a c4470 := h 4469 (by decide)
  have h6 : Entails.eval a c6382 := h 6381 (by decide)
  have h7 : Entails.eval a c6966 := h 6965 (by decide)
  have h8 : Entails.eval a c6936 := h 6935 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c7316 := h 7315 (by decide)
  have h11 : Entails.eval a c5713 := h 5712 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8044 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8044 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3488, some c3532, some c3747, some c3881, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p8044 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8044 : lratChecker f8044 p8044 = .success := by decide +kernel
theorem unsat8044 : Unsatisfiable (PosFin 65) f8044 := by
  apply lratCheckerSound f8044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8044
  · intro a ha; simp [p8044] at ha; subst a; trivial
  · exact checked8044
theorem derived8044 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8044 := by
  apply localUnsat_implies_entails f8044 [c3488, c3532, c3747, c3881] c8044 unsat8044 (by rfl) a
  have h0 : Entails.eval a c3488 := h 3487 (by decide)
  have h1 : Entails.eval a c3532 := h 3531 (by decide)
  have h2 : Entails.eval a c3747 := h 3746 (by decide)
  have h3 : Entails.eval a c3881 := h 3880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8045 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8045 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8043, some c8044, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p8045 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8045 : lratChecker f8045 p8045 = .success := by decide +kernel
theorem unsat8045 : Unsatisfiable (PosFin 65) f8045 := by
  apply lratCheckerSound f8045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8045
  · intro a ha; simp [p8045] at ha; subst a; trivial
  · exact checked8045
theorem derived8045 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8045 := by
  apply localUnsat_implies_entails f8045 [c8043, c8044] c8045 unsat8045 (by rfl) a
  have h0 : Entails.eval a c8043 := derived8043 a h
  have h1 : Entails.eval a c8044 := derived8044 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8046 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨43, by decide⟩, true), (⟨36, by decide⟩, false), (⟨1, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8046 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1879, some c1881, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p8046 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8046 : lratChecker f8046 p8046 = .success := by decide +kernel
theorem unsat8046 : Unsatisfiable (PosFin 65) f8046 := by
  apply lratCheckerSound f8046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8046
  · intro a ha; simp [p8046] at ha; subst a; trivial
  · exact checked8046
theorem derived8046 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8046 := by
  apply localUnsat_implies_entails f8046 [c1879, c1881] c8046 unsat8046 (by rfl) a
  have h0 : Entails.eval a c1879 := h 1878 (by decide)
  have h1 : Entails.eval a c1881 := h 1880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8047 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨45, by decide⟩, true), (⟨8, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8047 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3537, some c4990, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p8047 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8047 : lratChecker f8047 p8047 = .success := by decide +kernel
theorem unsat8047 : Unsatisfiable (PosFin 65) f8047 := by
  apply lratCheckerSound f8047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8047
  · intro a ha; simp [p8047] at ha; subst a; trivial
  · exact checked8047
theorem derived8047 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8047 := by
  apply localUnsat_implies_entails f8047 [c3537, c4990] c8047 unsat8047 (by rfl) a
  have h0 : Entails.eval a c3537 := h 3536 (by decide)
  have h1 : Entails.eval a c4990 := h 4989 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8048 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8048 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8041, some c8035, some c8007, some c8045, some c8013, some c8020, some c2069, some c1587, some c6382, some c6966, some c2760, some c3050, some c6936, some c2869, some c7316, some c6664, some c7364, some c6636, some c509, some c541, some c8046, some c8047, some c1784, some c3417, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8048 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked8048 : lratChecker f8048 p8048 = .success := by decide +kernel
theorem unsat8048 : Unsatisfiable (PosFin 65) f8048 := by
  apply lratCheckerSound f8048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8048
  · intro a ha; simp [p8048] at ha; subst a; trivial
  · exact checked8048
theorem derived8048 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8048 := by
  apply localUnsat_implies_entails f8048 [c8041, c8035, c8007, c8045, c8013, c8020, c2069, c1587, c6382, c6966, c2760, c3050, c6936, c2869, c7316, c6664, c7364, c6636, c509, c541, c8046, c8047, c1784, c3417] c8048 unsat8048 (by rfl) a
  have h0 : Entails.eval a c8041 := derived8041 a h
  have h1 : Entails.eval a c8035 := derived8035 a h
  have h2 : Entails.eval a c8007 := derived8007 a h
  have h3 : Entails.eval a c8045 := derived8045 a h
  have h4 : Entails.eval a c8013 := derived8013 a h
  have h5 : Entails.eval a c8020 := derived8020 a h
  have h6 : Entails.eval a c2069 := h 2068 (by decide)
  have h7 : Entails.eval a c1587 := h 1586 (by decide)
  have h8 : Entails.eval a c6382 := h 6381 (by decide)
  have h9 : Entails.eval a c6966 := h 6965 (by decide)
  have h10 : Entails.eval a c2760 := h 2759 (by decide)
  have h11 : Entails.eval a c3050 := h 3049 (by decide)
  have h12 : Entails.eval a c6936 := h 6935 (by decide)
  have h13 : Entails.eval a c2869 := h 2868 (by decide)
  have h14 : Entails.eval a c7316 := h 7315 (by decide)
  have h15 : Entails.eval a c6664 := h 6663 (by decide)
  have h16 : Entails.eval a c7364 := h 7363 (by decide)
  have h17 : Entails.eval a c6636 := h 6635 (by decide)
  have h18 : Entails.eval a c509 := h 508 (by decide)
  have h19 : Entails.eval a c541 := h 540 (by decide)
  have h20 : Entails.eval a c8046 := derived8046 a h
  have h21 : Entails.eval a c8047 := derived8047 a h
  have h22 : Entails.eval a c1784 := h 1783 (by decide)
  have h23 : Entails.eval a c3417 := h 3416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8049 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8049 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2963, some c3121, some c3667, some c3355, some c2521, some c2760, some c1114, some c4470, some c1587, some c4138, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8049 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8049 : lratChecker f8049 p8049 = .success := by decide +kernel
theorem unsat8049 : Unsatisfiable (PosFin 65) f8049 := by
  apply lratCheckerSound f8049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8049
  · intro a ha; simp [p8049] at ha; subst a; trivial
  · exact checked8049
theorem derived8049 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8049 := by
  apply localUnsat_implies_entails f8049 [c2963, c3121, c3667, c3355, c2521, c2760, c1114, c4470, c1587, c4138] c8049 unsat8049 (by rfl) a
  have h0 : Entails.eval a c2963 := h 2962 (by decide)
  have h1 : Entails.eval a c3121 := h 3120 (by decide)
  have h2 : Entails.eval a c3667 := h 3666 (by decide)
  have h3 : Entails.eval a c3355 := h 3354 (by decide)
  have h4 : Entails.eval a c2521 := h 2520 (by decide)
  have h5 : Entails.eval a c2760 := h 2759 (by decide)
  have h6 : Entails.eval a c1114 := h 1113 (by decide)
  have h7 : Entails.eval a c4470 := h 4469 (by decide)
  have h8 : Entails.eval a c1587 := h 1586 (by decide)
  have h9 : Entails.eval a c4138 := h 4137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8050 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8050 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8049, some c8024, some c1587, some c4051, some c3881, some c3355, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8050 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8050 : lratChecker f8050 p8050 = .success := by decide +kernel
theorem unsat8050 : Unsatisfiable (PosFin 65) f8050 := by
  apply lratCheckerSound f8050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8050
  · intro a ha; simp [p8050] at ha; subst a; trivial
  · exact checked8050
theorem derived8050 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8050 := by
  apply localUnsat_implies_entails f8050 [c8049, c8024, c1587, c4051, c3881, c3355] c8050 unsat8050 (by rfl) a
  have h0 : Entails.eval a c8049 := derived8049 a h
  have h1 : Entails.eval a c8024 := derived8024 a h
  have h2 : Entails.eval a c1587 := h 1586 (by decide)
  have h3 : Entails.eval a c4051 := h 4050 (by decide)
  have h4 : Entails.eval a c3881 := h 3880 (by decide)
  have h5 : Entails.eval a c3355 := h 3354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8050

end CochromaticTwenty.Certificates.FixedCore0
