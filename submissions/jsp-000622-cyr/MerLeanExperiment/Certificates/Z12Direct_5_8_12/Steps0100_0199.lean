import MerLeanExperiment.Certificates.Z12Direct_5_8_12.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_8_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1017 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1017 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c107, some c77, some c73, some c1016, some c188, some c696, some c105, some c902, some c362, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1017 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1017 : lratChecker f1017 p1017 = .success := by decide +kernel
theorem unsat1017 : Unsatisfiable (PosFin 31) f1017 := by
  apply lratCheckerSound f1017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1017
  · intro a ha; simp [p1017] at ha; subst a; trivial
  · exact checked1017
theorem derived1017 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1017 := by
  apply localUnsat_implies_entails f1017 [c107, c77, c73, c1016, c188, c696, c105, c902, c362] c1017 unsat1017 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c1016 := derived1016 a h
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c696 := h 695 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c902 := h 901 (by decide)
  have h8 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1018 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1018 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1011, some c968, some c73, some c77, some c107, some c1015, some c1017, some c691, some c1012, some c565, some c188, some c12, some c226, some c29, some c382, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1018 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1018 : lratChecker f1018 p1018 = .success := by decide +kernel
theorem unsat1018 : Unsatisfiable (PosFin 31) f1018 := by
  apply lratCheckerSound f1018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1018
  · intro a ha; simp [p1018] at ha; subst a; trivial
  · exact checked1018
theorem derived1018 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1018 := by
  apply localUnsat_implies_entails f1018 [c1011, c968, c73, c77, c107, c1015, c1017, c691, c1012, c565, c188, c12, c226, c29, c382] c1018 unsat1018 (by rfl) a
  have h0 : Entails.eval a c1011 := derived1011 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c1015 := derived1015 a h
  have h6 : Entails.eval a c1017 := derived1017 a h
  have h7 : Entails.eval a c691 := h 690 (by decide)
  have h8 : Entails.eval a c1012 := derived1012 a h
  have h9 : Entails.eval a c565 := h 564 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c226 := h 225 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1019 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1019 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c435, some c695, some c142, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1019 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1019 : lratChecker f1019 p1019 = .success := by decide +kernel
theorem unsat1019 : Unsatisfiable (PosFin 31) f1019 := by
  apply lratCheckerSound f1019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1019
  · intro a ha; simp [p1019] at ha; subst a; trivial
  · exact checked1019
theorem derived1019 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1019 := by
  apply localUnsat_implies_entails f1019 [c435, c695, c142] c1019 unsat1019 (by rfl) a
  have h0 : Entails.eval a c435 := h 434 (by decide)
  have h1 : Entails.eval a c695 := h 694 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1020 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1020 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c82, some c1012, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1020 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1020 : lratChecker f1020 p1020 = .success := by decide +kernel
theorem unsat1020 : Unsatisfiable (PosFin 31) f1020 := by
  apply lratCheckerSound f1020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1020
  · intro a ha; simp [p1020] at ha; subst a; trivial
  · exact checked1020
theorem derived1020 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1020 := by
  apply localUnsat_implies_entails f1020 [c82, c1012] c1020 unsat1020 (by rfl) a
  have h0 : Entails.eval a c82 := h 81 (by decide)
  have h1 : Entails.eval a c1012 := derived1012 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1021 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1021 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1019, some c1020, some c69, some c750, some c557, some c526, some c382, some c413, some c10, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1021 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1021 : lratChecker f1021 p1021 = .success := by decide +kernel
theorem unsat1021 : Unsatisfiable (PosFin 31) f1021 := by
  apply lratCheckerSound f1021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1021
  · intro a ha; simp [p1021] at ha; subst a; trivial
  · exact checked1021
theorem derived1021 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1021 := by
  apply localUnsat_implies_entails f1021 [c1019, c1020, c69, c750, c557, c526, c382, c413, c10] c1021 unsat1021 (by rfl) a
  have h0 : Entails.eval a c1019 := derived1019 a h
  have h1 : Entails.eval a c1020 := derived1020 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c750 := h 749 (by decide)
  have h4 : Entails.eval a c557 := h 556 (by decide)
  have h5 : Entails.eval a c526 := h 525 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c413 := h 412 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1022 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨13, by decide⟩, false), (⟨10, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1022 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c196, some c306, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1022 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1022 : lratChecker f1022 p1022 = .success := by decide +kernel
theorem unsat1022 : Unsatisfiable (PosFin 31) f1022 := by
  apply lratCheckerSound f1022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1022
  · intro a ha; simp [p1022] at ha; subst a; trivial
  · exact checked1022
theorem derived1022 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1022 := by
  apply localUnsat_implies_entails f1022 [c196, c306] c1022 unsat1022 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1023 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1023 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c69, some c152, some c430, some c741, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1023 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1023 : lratChecker f1023 p1023 = .success := by decide +kernel
theorem unsat1023 : Unsatisfiable (PosFin 31) f1023 := by
  apply lratCheckerSound f1023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1023
  · intro a ha; simp [p1023] at ha; subst a; trivial
  · exact checked1023
theorem derived1023 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1023 := by
  apply localUnsat_implies_entails f1023 [c69, c152, c430, c741] c1023 unsat1023 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c430 := h 429 (by decide)
  have h3 : Entails.eval a c741 := h 740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1024 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1024 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c69, some c1023, some c60, some c1022, some c55, some c91, some c59, some c108, some c193, some c303, some c207, some c741, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1024 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1024 : lratChecker f1024 p1024 = .success := by decide +kernel
theorem unsat1024 : Unsatisfiable (PosFin 31) f1024 := by
  apply lratCheckerSound f1024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1024
  · intro a ha; simp [p1024] at ha; subst a; trivial
  · exact checked1024
theorem derived1024 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1024 := by
  apply localUnsat_implies_entails f1024 [c69, c1023, c60, c1022, c55, c91, c59, c108, c193, c303, c207, c741] c1024 unsat1024 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c1023 := derived1023 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c1022 := derived1022 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c741 := h 740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1025 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1025 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c902, some c474, some c52, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1025 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1025 : lratChecker f1025 p1025 = .success := by decide +kernel
theorem unsat1025 : Unsatisfiable (PosFin 31) f1025 := by
  apply lratCheckerSound f1025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1025
  · intro a ha; simp [p1025] at ha; subst a; trivial
  · exact checked1025
theorem derived1025 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1025 := by
  apply localUnsat_implies_entails f1025 [c902, c474, c52] c1025 unsat1025 (by rfl) a
  have h0 : Entails.eval a c902 := h 901 (by decide)
  have h1 : Entails.eval a c474 := h 473 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1026 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1026 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c968, some c1021, some c1024, some c82, some c1025, some c859, some c190, some c136, some c83, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1026 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1026 : lratChecker f1026 p1026 = .success := by decide +kernel
theorem unsat1026 : Unsatisfiable (PosFin 31) f1026 := by
  apply lratCheckerSound f1026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1026
  · intro a ha; simp [p1026] at ha; subst a; trivial
  · exact checked1026
theorem derived1026 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1026 := by
  apply localUnsat_implies_entails f1026 [c968, c1021, c1024, c82, c1025, c859, c190, c136, c83] c1026 unsat1026 (by rfl) a
  have h0 : Entails.eval a c968 := derived968 a h
  have h1 : Entails.eval a c1021 := derived1021 a h
  have h2 : Entails.eval a c1024 := derived1024 a h
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c1025 := derived1025 a h
  have h5 : Entails.eval a c859 := h 858 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1027 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1027 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c429, some c431, some c754, some c60, some c614, some c251, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1027 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1027 : lratChecker f1027 p1027 = .success := by decide +kernel
theorem unsat1027 : Unsatisfiable (PosFin 31) f1027 := by
  apply lratCheckerSound f1027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1027
  · intro a ha; simp [p1027] at ha; subst a; trivial
  · exact checked1027
theorem derived1027 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1027 := by
  apply localUnsat_implies_entails f1027 [c429, c431, c754, c60, c614, c251] c1027 unsat1027 (by rfl) a
  have h0 : Entails.eval a c429 := h 428 (by decide)
  have h1 : Entails.eval a c431 := h 430 (by decide)
  have h2 : Entails.eval a c754 := h 753 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c614 := h 613 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1028 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1028 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1024, some c1027, some c741, some c152, some c547, some c395, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1028 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1028 : lratChecker f1028 p1028 = .success := by decide +kernel
theorem unsat1028 : Unsatisfiable (PosFin 31) f1028 := by
  apply lratCheckerSound f1028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1028
  · intro a ha; simp [p1028] at ha; subst a; trivial
  · exact checked1028
theorem derived1028 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1028 := by
  apply localUnsat_implies_entails f1028 [c1024, c1027, c741, c152, c547, c395] c1028 unsat1028 (by rfl) a
  have h0 : Entails.eval a c1024 := derived1024 a h
  have h1 : Entails.eval a c1027 := derived1027 a h
  have h2 : Entails.eval a c741 := h 740 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c547 := h 546 (by decide)
  have h5 : Entails.eval a c395 := h 394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1029 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1029 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c741, some c547, some c48, some c397, some c79, some c188, some c644, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1029 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1029 : lratChecker f1029 p1029 = .success := by decide +kernel
theorem unsat1029 : Unsatisfiable (PosFin 31) f1029 := by
  apply lratCheckerSound f1029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1029
  · intro a ha; simp [p1029] at ha; subst a; trivial
  · exact checked1029
theorem derived1029 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1029 := by
  apply localUnsat_implies_entails f1029 [c741, c547, c48, c397, c79, c188, c644] c1029 unsat1029 (by rfl) a
  have h0 : Entails.eval a c741 := h 740 (by decide)
  have h1 : Entails.eval a c547 := h 546 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c397 := h 396 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c644 := h 643 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1030 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1030 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1029, some c79, some c188, some c754, some c750, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1030 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1030 : lratChecker f1030 p1030 = .success := by decide +kernel
theorem unsat1030 : Unsatisfiable (PosFin 31) f1030 := by
  apply lratCheckerSound f1030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1030
  · intro a ha; simp [p1030] at ha; subst a; trivial
  · exact checked1030
theorem derived1030 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1030 := by
  apply localUnsat_implies_entails f1030 [c1029, c79, c188, c754, c750] c1030 unsat1030 (by rfl) a
  have h0 : Entails.eval a c1029 := derived1029 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c754 := h 753 (by decide)
  have h4 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1031 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨23, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1031 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c48, some c495, some c37, some c750, some c695, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1031 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1031 : lratChecker f1031 p1031 = .success := by decide +kernel
theorem unsat1031 : Unsatisfiable (PosFin 31) f1031 := by
  apply lratCheckerSound f1031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1031
  · intro a ha; simp [p1031] at ha; subst a; trivial
  · exact checked1031
theorem derived1031 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1031 := by
  apply localUnsat_implies_entails f1031 [c48, c495, c37, c750, c695] c1031 unsat1031 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c495 := h 494 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c750 := h 749 (by decide)
  have h4 : Entails.eval a c695 := h 694 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1032 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1032 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1011, some c968, some c1018, some c1026, some c90, some c1028, some c1029, some c1030, some c48, some c135, some c1031, some c45, some c190, some c126, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1032 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1032 : lratChecker f1032 p1032 = .success := by decide +kernel
theorem unsat1032 : Unsatisfiable (PosFin 31) f1032 := by
  apply lratCheckerSound f1032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1032
  · intro a ha; simp [p1032] at ha; subst a; trivial
  · exact checked1032
theorem derived1032 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1032 := by
  apply localUnsat_implies_entails f1032 [c1011, c968, c1018, c1026, c90, c1028, c1029, c1030, c48, c135, c1031, c45, c190, c126] c1032 unsat1032 (by rfl) a
  have h0 : Entails.eval a c1011 := derived1011 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c1018 := derived1018 a h
  have h3 : Entails.eval a c1026 := derived1026 a h
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c1028 := derived1028 a h
  have h6 : Entails.eval a c1029 := derived1029 a h
  have h7 : Entails.eval a c1030 := derived1030 a h
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  have h10 : Entails.eval a c1031 := derived1031 a h
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1033 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨7, by decide⟩, true), (⟨16, by decide⟩, false), (⟨21, by decide⟩, false), (⟨20, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1033 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c190, some c868, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1033 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1033 : lratChecker f1033 p1033 = .success := by decide +kernel
theorem unsat1033 : Unsatisfiable (PosFin 31) f1033 := by
  apply lratCheckerSound f1033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1033
  · intro a ha; simp [p1033] at ha; subst a; trivial
  · exact checked1033
theorem derived1033 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1033 := by
  apply localUnsat_implies_entails f1033 [c190, c868] c1033 unsat1033 (by rfl) a
  have h0 : Entails.eval a c190 := h 189 (by decide)
  have h1 : Entails.eval a c868 := h 867 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1034 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨8, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1034 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c48, some c41, some c740, some c387, some c1022, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1034 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1034 : lratChecker f1034 p1034 = .success := by decide +kernel
theorem unsat1034 : Unsatisfiable (PosFin 31) f1034 := by
  apply lratCheckerSound f1034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1034
  · intro a ha; simp [p1034] at ha; subst a; trivial
  · exact checked1034
theorem derived1034 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1034 := by
  apply localUnsat_implies_entails f1034 [c48, c41, c740, c387, c1022] c1034 unsat1034 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c740 := h 739 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c1022 := derived1022 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1035 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1035 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1032, some c1007, some c134, some c968, some c90, some c40, some c48, some c1034, some c4, some c429, some c562, some c203, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1035 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1035 : lratChecker f1035 p1035 = .success := by decide +kernel
theorem unsat1035 : Unsatisfiable (PosFin 31) f1035 := by
  apply lratCheckerSound f1035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1035
  · intro a ha; simp [p1035] at ha; subst a; trivial
  · exact checked1035
theorem derived1035 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1035 := by
  apply localUnsat_implies_entails f1035 [c1032, c1007, c134, c968, c90, c40, c48, c1034, c4, c429, c562, c203] c1035 unsat1035 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1007 := derived1007 a h
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c1034 := derived1034 a h
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c429 := h 428 (by decide)
  have h10 : Entails.eval a c562 := h 561 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1036 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1036 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1035, some c1032, some c1007, some c41, some c59, some c190, some c676, some c82, some c681, some c860, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1036 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1036 : lratChecker f1036 p1036 = .success := by decide +kernel
theorem unsat1036 : Unsatisfiable (PosFin 31) f1036 := by
  apply lratCheckerSound f1036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1036
  · intro a ha; simp [p1036] at ha; subst a; trivial
  · exact checked1036
theorem derived1036 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1036 := by
  apply localUnsat_implies_entails f1036 [c1035, c1032, c1007, c41, c59, c190, c676, c82, c681, c860] c1036 unsat1036 (by rfl) a
  have h0 : Entails.eval a c1035 := derived1035 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c1007 := derived1007 a h
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c676 := h 675 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c681 := h 680 (by decide)
  have h9 : Entails.eval a c860 := h 859 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1037 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1037 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1035, some c1032, some c1007, some c134, some c1011, some c968, some c1036, some c1019, some c48, some c750, some c320, some c207, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1037 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1037 : lratChecker f1037 p1037 = .success := by decide +kernel
theorem unsat1037 : Unsatisfiable (PosFin 31) f1037 := by
  apply lratCheckerSound f1037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1037
  · intro a ha; simp [p1037] at ha; subst a; trivial
  · exact checked1037
theorem derived1037 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1037 := by
  apply localUnsat_implies_entails f1037 [c1035, c1032, c1007, c134, c1011, c968, c1036, c1019, c48, c750, c320, c207] c1037 unsat1037 (by rfl) a
  have h0 : Entails.eval a c1035 := derived1035 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c1007 := derived1007 a h
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c1011 := derived1011 a h
  have h5 : Entails.eval a c968 := derived968 a h
  have h6 : Entails.eval a c1036 := derived1036 a h
  have h7 : Entails.eval a c1019 := derived1019 a h
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c750 := h 749 (by decide)
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1038 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1038 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1032, some c1007, some c134, some c968, some c1037, some c24, some c1034, some c284, some c258, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1038 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1038 : lratChecker f1038 p1038 = .success := by decide +kernel
theorem unsat1038 : Unsatisfiable (PosFin 31) f1038 := by
  apply lratCheckerSound f1038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1038
  · intro a ha; simp [p1038] at ha; subst a; trivial
  · exact checked1038
theorem derived1038 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1038 := by
  apply localUnsat_implies_entails f1038 [c1032, c1007, c134, c968, c1037, c24, c1034, c284, c258] c1038 unsat1038 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1007 := derived1007 a h
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c1037 := derived1037 a h
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c1034 := derived1034 a h
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1039 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1039 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c968, some c1011, some c1032, some c134, some c1007, some c1035, some c1038, some c65, some c195, some c69, some c284, some c305, some c216, some c48, some c41, some c890, some c467, some c466, some c112, some c724, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1039 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1039 : lratChecker f1039 p1039 = .success := by decide +kernel
theorem unsat1039 : Unsatisfiable (PosFin 31) f1039 := by
  apply lratCheckerSound f1039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1039
  · intro a ha; simp [p1039] at ha; subst a; trivial
  · exact checked1039
theorem derived1039 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1039 := by
  apply localUnsat_implies_entails f1039 [c968, c1011, c1032, c134, c1007, c1035, c1038, c65, c195, c69, c284, c305, c216, c48, c41, c890, c467, c466, c112, c724] c1039 unsat1039 (by rfl) a
  have h0 : Entails.eval a c968 := derived968 a h
  have h1 : Entails.eval a c1011 := derived1011 a h
  have h2 : Entails.eval a c1032 := derived1032 a h
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c1007 := derived1007 a h
  have h5 : Entails.eval a c1035 := derived1035 a h
  have h6 : Entails.eval a c1038 := derived1038 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c305 := h 304 (by decide)
  have h12 : Entails.eval a c216 := h 215 (by decide)
  have h13 : Entails.eval a c48 := h 47 (by decide)
  have h14 : Entails.eval a c41 := h 40 (by decide)
  have h15 : Entails.eval a c890 := h 889 (by decide)
  have h16 : Entails.eval a c467 := h 466 (by decide)
  have h17 : Entails.eval a c466 := h 465 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c724 := h 723 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1040 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨27, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1040 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c968, some c48, some c1039, some c716, some c874, some c1022, some c446, some c309, some c316, some c832, some c834, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1040 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1040 : lratChecker f1040 p1040 = .success := by decide +kernel
theorem unsat1040 : Unsatisfiable (PosFin 31) f1040 := by
  apply lratCheckerSound f1040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1040
  · intro a ha; simp [p1040] at ha; subst a; trivial
  · exact checked1040
theorem derived1040 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1040 := by
  apply localUnsat_implies_entails f1040 [c968, c48, c1039, c716, c874, c1022, c446, c309, c316, c832, c834] c1040 unsat1040 (by rfl) a
  have h0 : Entails.eval a c968 := derived968 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c716 := h 715 (by decide)
  have h4 : Entails.eval a c874 := h 873 (by decide)
  have h5 : Entails.eval a c1022 := derived1022 a h
  have h6 : Entails.eval a c446 := h 445 (by decide)
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c832 := h 831 (by decide)
  have h10 : Entails.eval a c834 := h 833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1041 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1041 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c968, some c48, some c1040, some c4, some c216, some c24, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1041 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1041 : lratChecker f1041 p1041 = .success := by decide +kernel
theorem unsat1041 : Unsatisfiable (PosFin 31) f1041 := by
  apply lratCheckerSound f1041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1041
  · intro a ha; simp [p1041] at ha; subst a; trivial
  · exact checked1041
theorem derived1041 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1041 := by
  apply localUnsat_implies_entails f1041 [c968, c48, c1040, c4, c216, c24] c1041 unsat1041 (by rfl) a
  have h0 : Entails.eval a c968 := derived968 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c1040 := derived1040 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1042 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1042 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c1041, some c66, some c81, some c188, some c796, some c110, some c716, some c454, some c798, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1042 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1042 : lratChecker f1042 p1042 = .success := by decide +kernel
theorem unsat1042 : Unsatisfiable (PosFin 31) f1042 := by
  apply lratCheckerSound f1042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1042
  · intro a ha; simp [p1042] at ha; subst a; trivial
  · exact checked1042
theorem derived1042 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1042 := by
  apply localUnsat_implies_entails f1042 [c1039, c1041, c66, c81, c188, c796, c110, c716, c454, c798] c1042 unsat1042 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c1041 := derived1041 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c796 := h 795 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c716 := h 715 (by decide)
  have h8 : Entails.eval a c454 := h 453 (by decide)
  have h9 : Entails.eval a c798 := h 797 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1043 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨14, by decide⟩, false), (⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1043 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c329, some c484, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1043 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1043 : lratChecker f1043 p1043 = .success := by decide +kernel
theorem unsat1043 : Unsatisfiable (PosFin 31) f1043 := by
  apply lratCheckerSound f1043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1043
  · intro a ha; simp [p1043] at ha; subst a; trivial
  · exact checked1043
theorem derived1043 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1043 := by
  apply localUnsat_implies_entails f1043 [c329, c484] c1043 unsat1043 (by rfl) a
  have h0 : Entails.eval a c329 := h 328 (by decide)
  have h1 : Entails.eval a c484 := h 483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1044 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1044 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c968, some c1041, some c79, some c66, some c81, some c188, some c110, some c796, some c21, some c1043, some c467, some c1042, some c180, some c556, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1044 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1044 : lratChecker f1044 p1044 = .success := by decide +kernel
theorem unsat1044 : Unsatisfiable (PosFin 31) f1044 := by
  apply lratCheckerSound f1044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1044
  · intro a ha; simp [p1044] at ha; subst a; trivial
  · exact checked1044
theorem derived1044 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1044 := by
  apply localUnsat_implies_entails f1044 [c1039, c968, c1041, c79, c66, c81, c188, c110, c796, c21, c1043, c467, c1042, c180, c556] c1044 unsat1044 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c1041 := derived1041 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c796 := h 795 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c1043 := derived1043 a h
  have h11 : Entails.eval a c467 := h 466 (by decide)
  have h12 : Entails.eval a c1042 := derived1042 a h
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c556 := h 555 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1045 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨8, by decide⟩, false), (⟨30, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1045 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1044, some c258, some c313, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1045 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1045 : lratChecker f1045 p1045 = .success := by decide +kernel
theorem unsat1045 : Unsatisfiable (PosFin 31) f1045 := by
  apply lratCheckerSound f1045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1045
  · intro a ha; simp [p1045] at ha; subst a; trivial
  · exact checked1045
theorem derived1045 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1045 := by
  apply localUnsat_implies_entails f1045 [c1044, c258, c313] c1045 unsat1045 (by rfl) a
  have h0 : Entails.eval a c1044 := derived1044 a h
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1046 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1046 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c968, some c1045, some c161, some c1041, some c79, some c66, some c81, some c188, some c796, some c21, some c559, some c882, some c472, some c899, some c76, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1046 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1046 : lratChecker f1046 p1046 = .success := by decide +kernel
theorem unsat1046 : Unsatisfiable (PosFin 31) f1046 := by
  apply lratCheckerSound f1046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1046
  · intro a ha; simp [p1046] at ha; subst a; trivial
  · exact checked1046
theorem derived1046 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1046 := by
  apply localUnsat_implies_entails f1046 [c1039, c968, c1045, c161, c1041, c79, c66, c81, c188, c796, c21, c559, c882, c472, c899, c76] c1046 unsat1046 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c1045 := derived1045 a h
  have h3 : Entails.eval a c161 := h 160 (by decide)
  have h4 : Entails.eval a c1041 := derived1041 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c796 := h 795 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c559 := h 558 (by decide)
  have h12 : Entails.eval a c882 := h 881 (by decide)
  have h13 : Entails.eval a c472 := h 471 (by decide)
  have h14 : Entails.eval a c899 := h 898 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1047 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1047 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1046, some c1039, some c968, some c1040, some c79, some c74, some c66, some c1012, some c1025, some c796, some c859, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1047 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1047 : lratChecker f1047 p1047 = .success := by decide +kernel
theorem unsat1047 : Unsatisfiable (PosFin 31) f1047 := by
  apply lratCheckerSound f1047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1047
  · intro a ha; simp [p1047] at ha; subst a; trivial
  · exact checked1047
theorem derived1047 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1047 := by
  apply localUnsat_implies_entails f1047 [c1046, c1039, c968, c1040, c79, c74, c66, c1012, c1025, c796, c859] c1047 unsat1047 (by rfl) a
  have h0 : Entails.eval a c1046 := derived1046 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c968 := derived968 a h
  have h3 : Entails.eval a c1040 := derived1040 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c1012 := derived1012 a h
  have h8 : Entails.eval a c1025 := derived1025 a h
  have h9 : Entails.eval a c796 := h 795 (by decide)
  have h10 : Entails.eval a c859 := h 858 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1048 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨2, by decide⟩, false), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1048 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c188, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1048 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1048 : lratChecker f1048 p1048 = .success := by decide +kernel
theorem unsat1048 : Unsatisfiable (PosFin 31) f1048 := by
  apply lratCheckerSound f1048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1048
  · intro a ha; simp [p1048] at ha; subst a; trivial
  · exact checked1048
theorem derived1048 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1048 := by
  apply localUnsat_implies_entails f1048 [c81, c188] c1048 unsat1048 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1049 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1049 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c968, some c1047, some c216, some c1048, some c48, some c195, some c24, some c680, some c306, some c501, some c481, some c479, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1049 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1049 : lratChecker f1049 p1049 = .success := by decide +kernel
theorem unsat1049 : Unsatisfiable (PosFin 31) f1049 := by
  apply lratCheckerSound f1049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1049
  · intro a ha; simp [p1049] at ha; subst a; trivial
  · exact checked1049
theorem derived1049 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1049 := by
  apply localUnsat_implies_entails f1049 [c1039, c968, c1047, c216, c1048, c48, c195, c24, c680, c306, c501, c481, c479] c1049 unsat1049 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c1047 := derived1047 a h
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c1048 := derived1048 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c680 := h 679 (by decide)
  have h9 : Entails.eval a c306 := h 305 (by decide)
  have h10 : Entails.eval a c501 := h 500 (by decide)
  have h11 : Entails.eval a c481 := h 480 (by decide)
  have h12 : Entails.eval a c479 := h 478 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1050 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1050 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1049, some c1046, some c1039, some c968, some c216, some c1048, some c48, some c195, some c24, some c470, some c1004, some c306, some c32, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1050 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1050 : lratChecker f1050 p1050 = .success := by decide +kernel
theorem unsat1050 : Unsatisfiable (PosFin 31) f1050 := by
  apply lratCheckerSound f1050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1050
  · intro a ha; simp [p1050] at ha; subst a; trivial
  · exact checked1050
theorem derived1050 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1050 := by
  apply localUnsat_implies_entails f1050 [c1049, c1046, c1039, c968, c216, c1048, c48, c195, c24, c470, c1004, c306, c32] c1050 unsat1050 (by rfl) a
  have h0 : Entails.eval a c1049 := derived1049 a h
  have h1 : Entails.eval a c1046 := derived1046 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c1048 := derived1048 a h
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c470 := h 469 (by decide)
  have h10 : Entails.eval a c1004 := derived1004 a h
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1051 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1051 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1046, some c1039, some c1049, some c1050, some c1040, some c81, some c110, some c1026, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1051 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1051 : lratChecker f1051 p1051 = .success := by decide +kernel
theorem unsat1051 : Unsatisfiable (PosFin 31) f1051 := by
  apply lratCheckerSound f1051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1051
  · intro a ha; simp [p1051] at ha; subst a; trivial
  · exact checked1051
theorem derived1051 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1051 := by
  apply localUnsat_implies_entails f1051 [c1046, c1039, c1049, c1050, c1040, c81, c110, c1026] c1051 unsat1051 (by rfl) a
  have h0 : Entails.eval a c1046 := derived1046 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c1049 := derived1049 a h
  have h3 : Entails.eval a c1050 := derived1050 a h
  have h4 : Entails.eval a c1040 := derived1040 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c1026 := derived1026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1052 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1052 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1046, some c1039, some c81, some c110, some c1026, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1052 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1052 : lratChecker f1052 p1052 = .success := by decide +kernel
theorem unsat1052 : Unsatisfiable (PosFin 31) f1052 := by
  apply lratCheckerSound f1052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1052
  · intro a ha; simp [p1052] at ha; subst a; trivial
  · exact checked1052
theorem derived1052 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1052 := by
  apply localUnsat_implies_entails f1052 [c1046, c1039, c81, c110, c1026] c1052 unsat1052 (by rfl) a
  have h0 : Entails.eval a c1046 := derived1046 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c1026 := derived1026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1053 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨27, by decide⟩, true), (⟨9, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1053 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c195, some c305, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1053 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1053 : lratChecker f1053 p1053 = .success := by decide +kernel
theorem unsat1053 : Unsatisfiable (PosFin 31) f1053 := by
  apply lratCheckerSound f1053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1053
  · intro a ha; simp [p1053] at ha; subst a; trivial
  · exact checked1053
theorem derived1053 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1053 := by
  apply localUnsat_implies_entails f1053 [c195, c305] c1053 unsat1053 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1054 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1054 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1051, some c1046, some c968, some c1052, some c1053, some c1004, some c1003, some c995, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1054 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1054 : lratChecker f1054 p1054 = .success := by decide +kernel
theorem unsat1054 : Unsatisfiable (PosFin 31) f1054 := by
  apply lratCheckerSound f1054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1054
  · intro a ha; simp [p1054] at ha; subst a; trivial
  · exact checked1054
theorem derived1054 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1054 := by
  apply localUnsat_implies_entails f1054 [c1051, c1046, c968, c1052, c1053, c1004, c1003, c995] c1054 unsat1054 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c1046 := derived1046 a h
  have h2 : Entails.eval a c968 := derived968 a h
  have h3 : Entails.eval a c1052 := derived1052 a h
  have h4 : Entails.eval a c1053 := derived1053 a h
  have h5 : Entails.eval a c1004 := derived1004 a h
  have h6 : Entails.eval a c1003 := derived1003 a h
  have h7 : Entails.eval a c995 := derived995 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1055 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨14, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1055 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1054, some c1051, some c1039, some c779, some c498, some c499, some c858, some c135, some c189, some c82, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1055 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1055 : lratChecker f1055 p1055 = .success := by decide +kernel
theorem unsat1055 : Unsatisfiable (PosFin 31) f1055 := by
  apply lratCheckerSound f1055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1055
  · intro a ha; simp [p1055] at ha; subst a; trivial
  · exact checked1055
theorem derived1055 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1055 := by
  apply localUnsat_implies_entails f1055 [c1054, c1051, c1039, c779, c498, c499, c858, c135, c189, c82] c1055 unsat1055 (by rfl) a
  have h0 : Entails.eval a c1054 := derived1054 a h
  have h1 : Entails.eval a c1051 := derived1051 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c779 := h 778 (by decide)
  have h4 : Entails.eval a c498 := h 497 (by decide)
  have h5 : Entails.eval a c499 := h 498 (by decide)
  have h6 : Entails.eval a c858 := h 857 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1056 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1056 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1051, some c1053, some c1054, some c1046, some c1039, some c968, some c1055, some c24, some c819, some c56, some c461, some c292, some c611, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1056 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1056 : lratChecker f1056 p1056 = .success := by decide +kernel
theorem unsat1056 : Unsatisfiable (PosFin 31) f1056 := by
  apply lratCheckerSound f1056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1056
  · intro a ha; simp [p1056] at ha; subst a; trivial
  · exact checked1056
theorem derived1056 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1056 := by
  apply localUnsat_implies_entails f1056 [c1051, c1053, c1054, c1046, c1039, c968, c1055, c24, c819, c56, c461, c292, c611] c1056 unsat1056 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c1053 := derived1053 a h
  have h2 : Entails.eval a c1054 := derived1054 a h
  have h3 : Entails.eval a c1046 := derived1046 a h
  have h4 : Entails.eval a c1039 := derived1039 a h
  have h5 : Entails.eval a c968 := derived968 a h
  have h6 : Entails.eval a c1055 := derived1055 a h
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c819 := h 818 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c461 := h 460 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c611 := h 610 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1057 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1057 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1051, some c1053, some c1054, some c1046, some c1039, some c968, some c1056, some c870, some c752, some c852, some c508, some c742, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1057 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1057 : lratChecker f1057 p1057 = .success := by decide +kernel
theorem unsat1057 : Unsatisfiable (PosFin 31) f1057 := by
  apply lratCheckerSound f1057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1057
  · intro a ha; simp [p1057] at ha; subst a; trivial
  · exact checked1057
theorem derived1057 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1057 := by
  apply localUnsat_implies_entails f1057 [c1051, c1053, c1054, c1046, c1039, c968, c1056, c870, c752, c852, c508, c742] c1057 unsat1057 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c1053 := derived1053 a h
  have h2 : Entails.eval a c1054 := derived1054 a h
  have h3 : Entails.eval a c1046 := derived1046 a h
  have h4 : Entails.eval a c1039 := derived1039 a h
  have h5 : Entails.eval a c968 := derived968 a h
  have h6 : Entails.eval a c1056 := derived1056 a h
  have h7 : Entails.eval a c870 := h 869 (by decide)
  have h8 : Entails.eval a c752 := h 751 (by decide)
  have h9 : Entails.eval a c852 := h 851 (by decide)
  have h10 : Entails.eval a c508 := h 507 (by decide)
  have h11 : Entails.eval a c742 := h 741 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1058 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1058 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c760, some c664, some c292, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1058 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1058 : lratChecker f1058 p1058 = .success := by decide +kernel
theorem unsat1058 : Unsatisfiable (PosFin 31) f1058 := by
  apply lratCheckerSound f1058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1058
  · intro a ha; simp [p1058] at ha; subst a; trivial
  · exact checked1058
theorem derived1058 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1058 := by
  apply localUnsat_implies_entails f1058 [c760, c664, c292] c1058 unsat1058 (by rfl) a
  have h0 : Entails.eval a c760 := h 759 (by decide)
  have h1 : Entails.eval a c664 := h 663 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1059 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1059 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1051, some c1046, some c1039, some c968, some c1053, some c1057, some c54, some c30, some c903, some c1058, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1059 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1059 : lratChecker f1059 p1059 = .success := by decide +kernel
theorem unsat1059 : Unsatisfiable (PosFin 31) f1059 := by
  apply lratCheckerSound f1059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1059
  · intro a ha; simp [p1059] at ha; subst a; trivial
  · exact checked1059
theorem derived1059 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1059 := by
  apply localUnsat_implies_entails f1059 [c1051, c1046, c1039, c968, c1053, c1057, c54, c30, c903, c1058] c1059 unsat1059 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c1046 := derived1046 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c1053 := derived1053 a h
  have h5 : Entails.eval a c1057 := derived1057 a h
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c903 := h 902 (by decide)
  have h9 : Entails.eval a c1058 := derived1058 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1060 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1060 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c968, some c1046, some c1051, some c1054, some c1059, some c79, some c74, some c66, some c1048, some c1012, some c255, some c716, some c1025, some c361, some c149, some c700, some c736, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1060 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1060 : lratChecker f1060 p1060 = .success := by decide +kernel
theorem unsat1060 : Unsatisfiable (PosFin 31) f1060 := by
  apply lratCheckerSound f1060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1060
  · intro a ha; simp [p1060] at ha; subst a; trivial
  · exact checked1060
theorem derived1060 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1060 := by
  apply localUnsat_implies_entails f1060 [c1039, c968, c1046, c1051, c1054, c1059, c79, c74, c66, c1048, c1012, c255, c716, c1025, c361, c149, c700, c736] c1060 unsat1060 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c1046 := derived1046 a h
  have h3 : Entails.eval a c1051 := derived1051 a h
  have h4 : Entails.eval a c1054 := derived1054 a h
  have h5 : Entails.eval a c1059 := derived1059 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c1048 := derived1048 a h
  have h10 : Entails.eval a c1012 := derived1012 a h
  have h11 : Entails.eval a c255 := h 254 (by decide)
  have h12 : Entails.eval a c716 := h 715 (by decide)
  have h13 : Entails.eval a c1025 := derived1025 a h
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c149 := h 148 (by decide)
  have h16 : Entails.eval a c700 := h 699 (by decide)
  have h17 : Entails.eval a c736 := h 735 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1061 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1061 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c1048, some c81, some c79, some c1060, some c190, some c618, some c127, some c875, some c83, some c255, some c430, some c462, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1061 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1061 : lratChecker f1061 p1061 = .success := by decide +kernel
theorem unsat1061 : Unsatisfiable (PosFin 31) f1061 := by
  apply lratCheckerSound f1061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1061
  · intro a ha; simp [p1061] at ha; subst a; trivial
  · exact checked1061
theorem derived1061 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1061 := by
  apply localUnsat_implies_entails f1061 [c1039, c1048, c81, c79, c1060, c190, c618, c127, c875, c83, c255, c430, c462] c1061 unsat1061 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c1060 := derived1060 a h
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c618 := h 617 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c875 := h 874 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c255 := h 254 (by decide)
  have h11 : Entails.eval a c430 := h 429 (by decide)
  have h12 : Entails.eval a c462 := h 461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1062 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1062 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1060, some c1039, some c79, some c1048, some c1061, some c620, some c21, some c207, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1062 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1062 : lratChecker f1062 p1062 = .success := by decide +kernel
theorem unsat1062 : Unsatisfiable (PosFin 31) f1062 := by
  apply lratCheckerSound f1062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1062
  · intro a ha; simp [p1062] at ha; subst a; trivial
  · exact checked1062
theorem derived1062 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1062 := by
  apply localUnsat_implies_entails f1062 [c1060, c1039, c79, c1048, c1061, c620, c21, c207] c1062 unsat1062 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1048 := derived1048 a h
  have h4 : Entails.eval a c1061 := derived1061 a h
  have h5 : Entails.eval a c620 := h 619 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1063 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨27, by decide⟩, true), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1063 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1060, some c1039, some c968, some c190, some c618, some c63, some c241, some c83, some c255, some c131, some c392, some c76, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1063 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1063 : lratChecker f1063 p1063 = .success := by decide +kernel
theorem unsat1063 : Unsatisfiable (PosFin 31) f1063 := by
  apply lratCheckerSound f1063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1063
  · intro a ha; simp [p1063] at ha; subst a; trivial
  · exact checked1063
theorem derived1063 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1063 := by
  apply localUnsat_implies_entails f1063 [c1060, c1039, c968, c190, c618, c63, c241, c83, c255, c131, c392, c76] c1063 unsat1063 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c968 := derived968 a h
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c618 := h 617 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c392 := h 391 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1064 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1064 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1062, some c1060, some c1039, some c968, some c874, some c1063, some c620, some c713, some c68, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1064 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1064 : lratChecker f1064 p1064 = .success := by decide +kernel
theorem unsat1064 : Unsatisfiable (PosFin 31) f1064 := by
  apply lratCheckerSound f1064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1064
  · intro a ha; simp [p1064] at ha; subst a; trivial
  · exact checked1064
theorem derived1064 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1064 := by
  apply localUnsat_implies_entails f1064 [c1062, c1060, c1039, c968, c874, c1063, c620, c713, c68] c1064 unsat1064 (by rfl) a
  have h0 : Entails.eval a c1062 := derived1062 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c874 := h 873 (by decide)
  have h5 : Entails.eval a c1063 := derived1063 a h
  have h6 : Entails.eval a c620 := h 619 (by decide)
  have h7 : Entails.eval a c713 := h 712 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1065 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1065 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c583, some c226, some c45, some c954, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1065 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1065 : lratChecker f1065 p1065 = .success := by decide +kernel
theorem unsat1065 : Unsatisfiable (PosFin 31) f1065 := by
  apply lratCheckerSound f1065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1065
  · intro a ha; simp [p1065] at ha; subst a; trivial
  · exact checked1065
theorem derived1065 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1065 := by
  apply localUnsat_implies_entails f1065 [c583, c226, c45, c954] c1065 unsat1065 (by rfl) a
  have h0 : Entails.eval a c583 := h 582 (by decide)
  have h1 : Entails.eval a c226 := h 225 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c954 := derived954 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1066 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1066 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c759, some c951, some c954, some c945, some c29, some c850, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1066 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1066 : lratChecker f1066 p1066 = .success := by decide +kernel
theorem unsat1066 : Unsatisfiable (PosFin 31) f1066 := by
  apply lratCheckerSound f1066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1066
  · intro a ha; simp [p1066] at ha; subst a; trivial
  · exact checked1066
theorem derived1066 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1066 := by
  apply localUnsat_implies_entails f1066 [c759, c951, c954, c945, c29, c850] c1066 unsat1066 (by rfl) a
  have h0 : Entails.eval a c759 := h 758 (by decide)
  have h1 : Entails.eval a c951 := derived951 a h
  have h2 : Entails.eval a c954 := derived954 a h
  have h3 : Entails.eval a c945 := derived945 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c850 := h 849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1067 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1067 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1064, some c1062, some c1060, some c1039, some c968, some c762, some c759, some c1065, some c1066, some c931, some c45, some c910, some c424, some c777, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1067 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1067 : lratChecker f1067 p1067 = .success := by decide +kernel
theorem unsat1067 : Unsatisfiable (PosFin 31) f1067 := by
  apply lratCheckerSound f1067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1067
  · intro a ha; simp [p1067] at ha; subst a; trivial
  · exact checked1067
theorem derived1067 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1067 := by
  apply localUnsat_implies_entails f1067 [c1064, c1062, c1060, c1039, c968, c762, c759, c1065, c1066, c931, c45, c910, c424, c777] c1067 unsat1067 (by rfl) a
  have h0 : Entails.eval a c1064 := derived1064 a h
  have h1 : Entails.eval a c1062 := derived1062 a h
  have h2 : Entails.eval a c1060 := derived1060 a h
  have h3 : Entails.eval a c1039 := derived1039 a h
  have h4 : Entails.eval a c968 := derived968 a h
  have h5 : Entails.eval a c762 := h 761 (by decide)
  have h6 : Entails.eval a c759 := h 758 (by decide)
  have h7 : Entails.eval a c1065 := derived1065 a h
  have h8 : Entails.eval a c1066 := derived1066 a h
  have h9 : Entails.eval a c931 := derived931 a h
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c910 := h 909 (by decide)
  have h12 : Entails.eval a c424 := h 423 (by decide)
  have h13 : Entails.eval a c777 := h 776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1068 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1068 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1060, some c1039, some c968, some c1062, some c1064, some c1067, some c190, some c83, some c218, some c136, some c892, some c468, some c142, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1068 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1068 : lratChecker f1068 p1068 = .success := by decide +kernel
theorem unsat1068 : Unsatisfiable (PosFin 31) f1068 := by
  apply lratCheckerSound f1068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1068
  · intro a ha; simp [p1068] at ha; subst a; trivial
  · exact checked1068
theorem derived1068 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1068 := by
  apply localUnsat_implies_entails f1068 [c1060, c1039, c968, c1062, c1064, c1067, c190, c83, c218, c136, c892, c468, c142] c1068 unsat1068 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c968 := derived968 a h
  have h3 : Entails.eval a c1062 := derived1062 a h
  have h4 : Entails.eval a c1064 := derived1064 a h
  have h5 : Entails.eval a c1067 := derived1067 a h
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c892 := h 891 (by decide)
  have h11 : Entails.eval a c468 := h 467 (by decide)
  have h12 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1069 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1069 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c1048, some c1068, some c1060, some c190, some c83, some c218, some c136, some c542, some c892, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1069 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1069 : lratChecker f1069 p1069 = .success := by decide +kernel
theorem unsat1069 : Unsatisfiable (PosFin 31) f1069 := by
  apply lratCheckerSound f1069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1069
  · intro a ha; simp [p1069] at ha; subst a; trivial
  · exact checked1069
theorem derived1069 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1069 := by
  apply localUnsat_implies_entails f1069 [c1039, c1048, c1068, c1060, c190, c83, c218, c136, c542, c892] c1069 unsat1069 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c1068 := derived1068 a h
  have h3 : Entails.eval a c1060 := derived1060 a h
  have h4 : Entails.eval a c190 := h 189 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c542 := h 541 (by decide)
  have h9 : Entails.eval a c892 := h 891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1070 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨17, by decide⟩, true), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1070 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1048, some c895, some c544, some c696, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1070 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1070 : lratChecker f1070 p1070 = .success := by decide +kernel
theorem unsat1070 : Unsatisfiable (PosFin 31) f1070 := by
  apply lratCheckerSound f1070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1070
  · intro a ha; simp [p1070] at ha; subst a; trivial
  · exact checked1070
theorem derived1070 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1070 := by
  apply localUnsat_implies_entails f1070 [c1048, c895, c544, c696] c1070 unsat1070 (by rfl) a
  have h0 : Entails.eval a c1048 := derived1048 a h
  have h1 : Entails.eval a c895 := h 894 (by decide)
  have h2 : Entails.eval a c544 := h 543 (by decide)
  have h3 : Entails.eval a c696 := h 695 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1071 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1071 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1069, some c1039, some c1048, some c1068, some c1060, some c968, some c1070, some c48, some c332, some c207, some c193, some c542, some c892, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1071 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1071 : lratChecker f1071 p1071 = .success := by decide +kernel
theorem unsat1071 : Unsatisfiable (PosFin 31) f1071 := by
  apply lratCheckerSound f1071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1071
  · intro a ha; simp [p1071] at ha; subst a; trivial
  · exact checked1071
theorem derived1071 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1071 := by
  apply localUnsat_implies_entails f1071 [c1069, c1039, c1048, c1068, c1060, c968, c1070, c48, c332, c207, c193, c542, c892] c1071 unsat1071 (by rfl) a
  have h0 : Entails.eval a c1069 := derived1069 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c1048 := derived1048 a h
  have h3 : Entails.eval a c1068 := derived1068 a h
  have h4 : Entails.eval a c1060 := derived1060 a h
  have h5 : Entails.eval a c968 := derived968 a h
  have h6 : Entails.eval a c1070 := derived1070 a h
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c332 := h 331 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c193 := h 192 (by decide)
  have h11 : Entails.eval a c542 := h 541 (by decide)
  have h12 : Entails.eval a c892 := h 891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1072 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1072 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1068, some c1060, some c1039, some c968, some c1048, some c1071, some c331, some c29, some c272, some c495, some c15, some c863, some c842, some c211, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1072 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1072 : lratChecker f1072 p1072 = .success := by decide +kernel
theorem unsat1072 : Unsatisfiable (PosFin 31) f1072 := by
  apply lratCheckerSound f1072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1072
  · intro a ha; simp [p1072] at ha; subst a; trivial
  · exact checked1072
theorem derived1072 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1072 := by
  apply localUnsat_implies_entails f1072 [c1068, c1060, c1039, c968, c1048, c1071, c331, c29, c272, c495, c15, c863, c842, c211] c1072 unsat1072 (by rfl) a
  have h0 : Entails.eval a c1068 := derived1068 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c1048 := derived1048 a h
  have h5 : Entails.eval a c1071 := derived1071 a h
  have h6 : Entails.eval a c331 := h 330 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c495 := h 494 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c863 := h 862 (by decide)
  have h12 : Entails.eval a c842 := h 841 (by decide)
  have h13 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1073 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1073 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1072, some c1068, some c1039, some c968, some c292, some c16, some c152, some c142, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1073 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1073 : lratChecker f1073 p1073 = .success := by decide +kernel
theorem unsat1073 : Unsatisfiable (PosFin 31) f1073 := by
  apply lratCheckerSound f1073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1073
  · intro a ha; simp [p1073] at ha; subst a; trivial
  · exact checked1073
theorem derived1073 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1073 := by
  apply localUnsat_implies_entails f1073 [c1072, c1068, c1039, c968, c292, c16, c152, c142] c1073 unsat1073 (by rfl) a
  have h0 : Entails.eval a c1072 := derived1072 a h
  have h1 : Entails.eval a c1068 := derived1068 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1074 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1074 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1060, some c1039, some c968, some c1068, some c1072, some c1073, some c14, some c2, some c207, some c714, some c878, some c447, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1074 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1074 : lratChecker f1074 p1074 = .success := by decide +kernel
theorem unsat1074 : Unsatisfiable (PosFin 31) f1074 := by
  apply lratCheckerSound f1074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1074
  · intro a ha; simp [p1074] at ha; subst a; trivial
  · exact checked1074
theorem derived1074 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1074 := by
  apply localUnsat_implies_entails f1074 [c1060, c1039, c968, c1068, c1072, c1073, c14, c2, c207, c714, c878, c447] c1074 unsat1074 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c968 := derived968 a h
  have h3 : Entails.eval a c1068 := derived1068 a h
  have h4 : Entails.eval a c1072 := derived1072 a h
  have h5 : Entails.eval a c1073 := derived1073 a h
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c714 := h 713 (by decide)
  have h10 : Entails.eval a c878 := h 877 (by decide)
  have h11 : Entails.eval a c447 := h 446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1075 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1075 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c714, some c878, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1075 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1075 : lratChecker f1075 p1075 = .success := by decide +kernel
theorem unsat1075 : Unsatisfiable (PosFin 31) f1075 := by
  apply lratCheckerSound f1075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1075
  · intro a ha; simp [p1075] at ha; subst a; trivial
  · exact checked1075
theorem derived1075 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1075 := by
  apply localUnsat_implies_entails f1075 [c714, c878] c1075 unsat1075 (by rfl) a
  have h0 : Entails.eval a c714 := h 713 (by decide)
  have h1 : Entails.eval a c878 := h 877 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1076 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1076 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c968, some c152, some c259, some c52, some c153, some c314, some c446, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1076 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1076 : lratChecker f1076 p1076 = .success := by decide +kernel
theorem unsat1076 : Unsatisfiable (PosFin 31) f1076 := by
  apply lratCheckerSound f1076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1076
  · intro a ha; simp [p1076] at ha; subst a; trivial
  · exact checked1076
theorem derived1076 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1076 := by
  apply localUnsat_implies_entails f1076 [c1039, c968, c152, c259, c52, c153, c314, c446] c1076 unsat1076 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c153 := h 152 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c446 := h 445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1077 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1077 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1074, some c1060, some c1039, some c968, some c1076, some c714, some c1075, some c196, some c447, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1077 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1077 : lratChecker f1077 p1077 = .success := by decide +kernel
theorem unsat1077 : Unsatisfiable (PosFin 31) f1077 := by
  apply lratCheckerSound f1077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1077
  · intro a ha; simp [p1077] at ha; subst a; trivial
  · exact checked1077
theorem derived1077 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1077 := by
  apply localUnsat_implies_entails f1077 [c1074, c1060, c1039, c968, c1076, c714, c1075, c196, c447] c1077 unsat1077 (by rfl) a
  have h0 : Entails.eval a c1074 := derived1074 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c1076 := derived1076 a h
  have h5 : Entails.eval a c714 := h 713 (by decide)
  have h6 : Entails.eval a c1075 := derived1075 a h
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c447 := h 446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1078 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1078 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1074, some c1060, some c1039, some c968, some c1077, some c1048, some c24, some c331, some c29, some c272, some c495, some c15, some c19, some c547, some c38, some c48, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1078 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1078 : lratChecker f1078 p1078 = .success := by decide +kernel
theorem unsat1078 : Unsatisfiable (PosFin 31) f1078 := by
  apply lratCheckerSound f1078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1078
  · intro a ha; simp [p1078] at ha; subst a; trivial
  · exact checked1078
theorem derived1078 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1078 := by
  apply localUnsat_implies_entails f1078 [c1074, c1060, c1039, c968, c1077, c1048, c24, c331, c29, c272, c495, c15, c19, c547, c38, c48] c1078 unsat1078 (by rfl) a
  have h0 : Entails.eval a c1074 := derived1074 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c1048 := derived1048 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c495 := h 494 (by decide)
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c547 := h 546 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1079 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1079 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1078, some c1074, some c1060, some c1039, some c968, some c1048, some c24, some c331, some c29, some c272, some c532, some c741, some c19, some c196, some c579, some c844, some c139, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1079 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1079 : lratChecker f1079 p1079 = .success := by decide +kernel
theorem unsat1079 : Unsatisfiable (PosFin 31) f1079 := by
  apply lratCheckerSound f1079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1079
  · intro a ha; simp [p1079] at ha; subst a; trivial
  · exact checked1079
theorem derived1079 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1079 := by
  apply localUnsat_implies_entails f1079 [c1078, c1074, c1060, c1039, c968, c1048, c24, c331, c29, c272, c532, c741, c19, c196, c579, c844, c139] c1079 unsat1079 (by rfl) a
  have h0 : Entails.eval a c1078 := derived1078 a h
  have h1 : Entails.eval a c1074 := derived1074 a h
  have h2 : Entails.eval a c1060 := derived1060 a h
  have h3 : Entails.eval a c1039 := derived1039 a h
  have h4 : Entails.eval a c968 := derived968 a h
  have h5 : Entails.eval a c1048 := derived1048 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c532 := h 531 (by decide)
  have h11 : Entails.eval a c741 := h 740 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c579 := h 578 (by decide)
  have h15 : Entails.eval a c844 := h 843 (by decide)
  have h16 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1080 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1080 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c874, some c24, some c196, some c203, some c446, some c8, some c309, some c447, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1080 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1080 : lratChecker f1080 p1080 = .success := by decide +kernel
theorem unsat1080 : Unsatisfiable (PosFin 31) f1080 := by
  apply lratCheckerSound f1080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1080
  · intro a ha; simp [p1080] at ha; subst a; trivial
  · exact checked1080
theorem derived1080 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1080 := by
  apply localUnsat_implies_entails f1080 [c874, c24, c196, c203, c446, c8, c309, c447] c1080 unsat1080 (by rfl) a
  have h0 : Entails.eval a c874 := h 873 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c446 := h 445 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c447 := h 446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1081 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1081 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1039, some c968, some c1060, some c1074, some c1078, some c1079, some c1080, some c81, some c618, some c255, some c796, some c240, some c307, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1081 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1081 : lratChecker f1081 p1081 = .success := by decide +kernel
theorem unsat1081 : Unsatisfiable (PosFin 31) f1081 := by
  apply lratCheckerSound f1081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1081
  · intro a ha; simp [p1081] at ha; subst a; trivial
  · exact checked1081
theorem derived1081 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1081 := by
  apply localUnsat_implies_entails f1081 [c1039, c968, c1060, c1074, c1078, c1079, c1080, c81, c618, c255, c796, c240, c307] c1081 unsat1081 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c1060 := derived1060 a h
  have h3 : Entails.eval a c1074 := derived1074 a h
  have h4 : Entails.eval a c1078 := derived1078 a h
  have h5 : Entails.eval a c1079 := derived1079 a h
  have h6 : Entails.eval a c1080 := derived1080 a h
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c618 := h 617 (by decide)
  have h9 : Entails.eval a c255 := h 254 (by decide)
  have h10 : Entails.eval a c796 := h 795 (by decide)
  have h11 : Entails.eval a c240 := h 239 (by decide)
  have h12 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1082 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1082 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c968, some c1039, some c1060, some c1074, some c1078, some c1079, some c1080, some c79, some c81, some c1081, some c620, some c713, some c21, some c45, some c621, some c318, some c879, some c166, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1082 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1082 : lratChecker f1082 p1082 = .success := by decide +kernel
theorem unsat1082 : Unsatisfiable (PosFin 31) f1082 := by
  apply lratCheckerSound f1082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1082
  · intro a ha; simp [p1082] at ha; subst a; trivial
  · exact checked1082
theorem derived1082 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1082 := by
  apply localUnsat_implies_entails f1082 [c968, c1039, c1060, c1074, c1078, c1079, c1080, c79, c81, c1081, c620, c713, c21, c45, c621, c318, c879, c166] c1082 unsat1082 (by rfl) a
  have h0 : Entails.eval a c968 := derived968 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c1060 := derived1060 a h
  have h3 : Entails.eval a c1074 := derived1074 a h
  have h4 : Entails.eval a c1078 := derived1078 a h
  have h5 : Entails.eval a c1079 := derived1079 a h
  have h6 : Entails.eval a c1080 := derived1080 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c1081 := derived1081 a h
  have h10 : Entails.eval a c620 := h 619 (by decide)
  have h11 : Entails.eval a c713 := h 712 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c621 := h 620 (by decide)
  have h15 : Entails.eval a c318 := h 317 (by decide)
  have h16 : Entails.eval a c879 := h 878 (by decide)
  have h17 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1083 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1083 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c67, some c68, some c711, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1083 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1083 : lratChecker f1083 p1083 = .success := by decide +kernel
theorem unsat1083 : Unsatisfiable (PosFin 31) f1083 := by
  apply lratCheckerSound f1083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1083
  · intro a ha; simp [p1083] at ha; subst a; trivial
  · exact checked1083
theorem derived1083 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1083 := by
  apply localUnsat_implies_entails f1083 [c1082, c67, c68, c711] c1083 unsat1083 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c711 := h 710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1084 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1084 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c621, some c255, some c448, some c1083, some c713, some c136, some c83, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1084 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1084 : lratChecker f1084 p1084 = .success := by decide +kernel
theorem unsat1084 : Unsatisfiable (PosFin 31) f1084 := by
  apply lratCheckerSound f1084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1084
  · intro a ha; simp [p1084] at ha; subst a; trivial
  · exact checked1084
theorem derived1084 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1084 := by
  apply localUnsat_implies_entails f1084 [c621, c255, c448, c1083, c713, c136, c83] c1084 unsat1084 (by rfl) a
  have h0 : Entails.eval a c621 := h 620 (by decide)
  have h1 : Entails.eval a c255 := h 254 (by decide)
  have h2 : Entails.eval a c448 := h 447 (by decide)
  have h3 : Entails.eval a c1083 := derived1083 a h
  have h4 : Entails.eval a c713 := h 712 (by decide)
  have h5 : Entails.eval a c136 := h 135 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1085 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1085 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c1084, some c620, some c78, some c618, some c26, some c255, some c586, some c307, some c796, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1085 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1085 : lratChecker f1085 p1085 = .success := by decide +kernel
theorem unsat1085 : Unsatisfiable (PosFin 31) f1085 := by
  apply lratCheckerSound f1085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1085
  · intro a ha; simp [p1085] at ha; subst a; trivial
  · exact checked1085
theorem derived1085 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1085 := by
  apply localUnsat_implies_entails f1085 [c1082, c1084, c620, c78, c618, c26, c255, c586, c307, c796] c1085 unsat1085 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c1084 := derived1084 a h
  have h2 : Entails.eval a c620 := h 619 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c618 := h 617 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c586 := h 585 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c796 := h 795 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1086 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1086 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c255, some c586, some c796, some c69, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1086 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1086 : lratChecker f1086 p1086 = .success := by decide +kernel
theorem unsat1086 : Unsatisfiable (PosFin 31) f1086 := by
  apply lratCheckerSound f1086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1086
  · intro a ha; simp [p1086] at ha; subst a; trivial
  · exact checked1086
theorem derived1086 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1086 := by
  apply localUnsat_implies_entails f1086 [c255, c586, c796, c69] c1086 unsat1086 (by rfl) a
  have h0 : Entails.eval a c255 := h 254 (by decide)
  have h1 : Entails.eval a c586 := h 585 (by decide)
  have h2 : Entails.eval a c796 := h 795 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1087 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1087 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1085, some c1082, some c78, some c26, some c711, some c1086, some c50, some c715, some c136, some c83, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1087 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1087 : lratChecker f1087 p1087 = .success := by decide +kernel
theorem unsat1087 : Unsatisfiable (PosFin 31) f1087 := by
  apply lratCheckerSound f1087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1087
  · intro a ha; simp [p1087] at ha; subst a; trivial
  · exact checked1087
theorem derived1087 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1087 := by
  apply localUnsat_implies_entails f1087 [c1085, c1082, c78, c26, c711, c1086, c50, c715, c136, c83] c1087 unsat1087 (by rfl) a
  have h0 : Entails.eval a c1085 := derived1085 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c711 := h 710 (by decide)
  have h5 : Entails.eval a c1086 := derived1086 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c715 := h 714 (by decide)
  have h8 : Entails.eval a c136 := h 135 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1088 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1088 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c798, some c69, some c528, some c56, some c139, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1088 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1088 : lratChecker f1088 p1088 = .success := by decide +kernel
theorem unsat1088 : Unsatisfiable (PosFin 31) f1088 := by
  apply lratCheckerSound f1088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1088
  · intro a ha; simp [p1088] at ha; subst a; trivial
  · exact checked1088
theorem derived1088 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1088 := by
  apply localUnsat_implies_entails f1088 [c798, c69, c528, c56, c139] c1088 unsat1088 (by rfl) a
  have h0 : Entails.eval a c798 := h 797 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c528 := h 527 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1089 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1089 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c1085, some c1087, some c46, some c255, some c1088, some c448, some c1083, some c876, some c69, some c528, some c511, some c915, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1089 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1089 : lratChecker f1089 p1089 = .success := by decide +kernel
theorem unsat1089 : Unsatisfiable (PosFin 31) f1089 := by
  apply lratCheckerSound f1089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1089
  · intro a ha; simp [p1089] at ha; subst a; trivial
  · exact checked1089
theorem derived1089 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1089 := by
  apply localUnsat_implies_entails f1089 [c1082, c1085, c1087, c46, c255, c1088, c448, c1083, c876, c69, c528, c511, c915] c1089 unsat1089 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c1085 := derived1085 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c1088 := derived1088 a h
  have h6 : Entails.eval a c448 := h 447 (by decide)
  have h7 : Entails.eval a c1083 := derived1083 a h
  have h8 : Entails.eval a c876 := h 875 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c528 := h 527 (by decide)
  have h11 : Entails.eval a c511 := h 510 (by decide)
  have h12 : Entails.eval a c915 := h 914 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1090 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1090 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c16, some c606, some c28, some c22, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1090 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1090 : lratChecker f1090 p1090 = .success := by decide +kernel
theorem unsat1090 : Unsatisfiable (PosFin 31) f1090 := by
  apply lratCheckerSound f1090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1090
  · intro a ha; simp [p1090] at ha; subst a; trivial
  · exact checked1090
theorem derived1090 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1090 := by
  apply localUnsat_implies_entails f1090 [c16, c606, c28, c22] c1090 unsat1090 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c606 := h 605 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1091 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨24, by decide⟩, false), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1091 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c207, some c319, some c262, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1091 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1091 : lratChecker f1091 p1091 = .success := by decide +kernel
theorem unsat1091 : Unsatisfiable (PosFin 31) f1091 := by
  apply lratCheckerSound f1091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1091
  · intro a ha; simp [p1091] at ha; subst a; trivial
  · exact checked1091
theorem derived1091 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1091 := by
  apply localUnsat_implies_entails f1091 [c207, c319, c262] c1091 unsat1091 (by rfl) a
  have h0 : Entails.eval a c207 := h 206 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1092 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1092 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1089, some c1082, some c46, some c255, some c1090, some c1091, some c22, some c14, some c376, some c251, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1092 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1092 : lratChecker f1092 p1092 = .success := by decide +kernel
theorem unsat1092 : Unsatisfiable (PosFin 31) f1092 := by
  apply lratCheckerSound f1092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1092
  · intro a ha; simp [p1092] at ha; subst a; trivial
  · exact checked1092
theorem derived1092 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1092 := by
  apply localUnsat_implies_entails f1092 [c1089, c1082, c46, c255, c1090, c1091, c22, c14, c376, c251] c1092 unsat1092 (by rfl) a
  have h0 : Entails.eval a c1089 := derived1089 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c1090 := derived1090 a h
  have h5 : Entails.eval a c1091 := derived1091 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1093 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1093 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1089, some c1082, some c78, some c190, some c711, some c83, some c241, some c86, some c16, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1093 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1093 : lratChecker f1093 p1093 = .success := by decide +kernel
theorem unsat1093 : Unsatisfiable (PosFin 31) f1093 := by
  apply lratCheckerSound f1093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1093
  · intro a ha; simp [p1093] at ha; subst a; trivial
  · exact checked1093
theorem derived1093 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1093 := by
  apply localUnsat_implies_entails f1093 [c1089, c1082, c78, c190, c711, c83, c241, c86, c16] c1093 unsat1093 (by rfl) a
  have h0 : Entails.eval a c1089 := derived1089 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c711 := h 710 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1094 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1094 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1092, some c1084, some c620, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1094 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1094 : lratChecker f1094 p1094 = .success := by decide +kernel
theorem unsat1094 : Unsatisfiable (PosFin 31) f1094 := by
  apply lratCheckerSound f1094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1094
  · intro a ha; simp [p1094] at ha; subst a; trivial
  · exact checked1094
theorem derived1094 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1094 := by
  apply localUnsat_implies_entails f1094 [c1092, c1084, c620] c1094 unsat1094 (by rfl) a
  have h0 : Entails.eval a c1092 := derived1092 a h
  have h1 : Entails.eval a c1084 := derived1084 a h
  have h2 : Entails.eval a c620 := h 619 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1095 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨30, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1095 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1093, some c1094, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1095 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1095 : lratChecker f1095 p1095 = .success := by decide +kernel
theorem unsat1095 : Unsatisfiable (PosFin 31) f1095 := by
  apply lratCheckerSound f1095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1095
  · intro a ha; simp [p1095] at ha; subst a; trivial
  · exact checked1095
theorem derived1095 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1095 := by
  apply localUnsat_implies_entails f1095 [c1093, c1094] c1095 unsat1095 (by rfl) a
  have h0 : Entails.eval a c1093 := derived1093 a h
  have h1 : Entails.eval a c1094 := derived1094 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1096 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1096 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c619, some c52, some c712, some c312, some c257, some c157, some c1075, some c447, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1096 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1096 : lratChecker f1096 p1096 = .success := by decide +kernel
theorem unsat1096 : Unsatisfiable (PosFin 31) f1096 := by
  apply lratCheckerSound f1096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1096
  · intro a ha; simp [p1096] at ha; subst a; trivial
  · exact checked1096
theorem derived1096 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1096 := by
  apply localUnsat_implies_entails f1096 [c619, c52, c712, c312, c257, c157, c1075, c447] c1096 unsat1096 (by rfl) a
  have h0 : Entails.eval a c619 := h 618 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c712 := h 711 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  have h6 : Entails.eval a c1075 := derived1075 a h
  have h7 : Entails.eval a c447 := h 446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1097 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, true), (⟨30, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1097 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c801, some c448, some c152, some c259, some c314, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1097 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1097 : lratChecker f1097 p1097 = .success := by decide +kernel
theorem unsat1097 : Unsatisfiable (PosFin 31) f1097 := by
  apply lratCheckerSound f1097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1097
  · intro a ha; simp [p1097] at ha; subst a; trivial
  · exact checked1097
theorem derived1097 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1097 := by
  apply localUnsat_implies_entails f1097 [c801, c448, c152, c259, c314] c1097 unsat1097 (by rfl) a
  have h0 : Entails.eval a c801 := h 800 (by decide)
  have h1 : Entails.eval a c448 := h 447 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1098 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1098 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c619, some c1096, some c52, some c712, some c312, some c257, some c157, some c26, some c447, some c701, some c545, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1098 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1098 : lratChecker f1098 p1098 = .success := by decide +kernel
theorem unsat1098 : Unsatisfiable (PosFin 31) f1098 := by
  apply lratCheckerSound f1098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1098
  · intro a ha; simp [p1098] at ha; subst a; trivial
  · exact checked1098
theorem derived1098 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1098 := by
  apply localUnsat_implies_entails f1098 [c619, c1096, c52, c712, c312, c257, c157, c26, c447, c701, c545] c1098 unsat1098 (by rfl) a
  have h0 : Entails.eval a c619 := h 618 (by decide)
  have h1 : Entails.eval a c1096 := derived1096 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c712 := h 711 (by decide)
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c257 := h 256 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c447 := h 446 (by decide)
  have h9 : Entails.eval a c701 := h 700 (by decide)
  have h10 : Entails.eval a c545 := h 544 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1099 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1099 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1098, some c50, some c447, some c255, some c48, some c797, some c802, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1099 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1099 : lratChecker f1099 p1099 = .success := by decide +kernel
theorem unsat1099 : Unsatisfiable (PosFin 31) f1099 := by
  apply lratCheckerSound f1099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1099
  · intro a ha; simp [p1099] at ha; subst a; trivial
  · exact checked1099
theorem derived1099 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1099 := by
  apply localUnsat_implies_entails f1099 [c1098, c50, c447, c255, c48, c797, c802] c1099 unsat1099 (by rfl) a
  have h0 : Entails.eval a c1098 := derived1098 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c447 := h 446 (by decide)
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c797 := h 796 (by decide)
  have h6 : Entails.eval a c802 := h 801 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1100 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1100 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c1095, some c1097, some c1098, some c78, some c1099, some c52, some c446, some c797, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1100 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1100 : lratChecker f1100 p1100 = .success := by decide +kernel
theorem unsat1100 : Unsatisfiable (PosFin 31) f1100 := by
  apply lratCheckerSound f1100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1100
  · intro a ha; simp [p1100] at ha; subst a; trivial
  · exact checked1100
theorem derived1100 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1100 := by
  apply localUnsat_implies_entails f1100 [c1082, c1095, c1097, c1098, c78, c1099, c52, c446, c797] c1100 unsat1100 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c1095 := derived1095 a h
  have h2 : Entails.eval a c1097 := derived1097 a h
  have h3 : Entails.eval a c1098 := derived1098 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c1099 := derived1099 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c446 := h 445 (by decide)
  have h8 : Entails.eval a c797 := h 796 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1101 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1101 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c52, some c152, some c1100, some c78, some c136, some c83, some c190, some c473, some c17, some c58, some c463, some c866, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1101 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1101 : lratChecker f1101 p1101 = .success := by decide +kernel
theorem unsat1101 : Unsatisfiable (PosFin 31) f1101 := by
  apply lratCheckerSound f1101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1101
  · intro a ha; simp [p1101] at ha; subst a; trivial
  · exact checked1101
theorem derived1101 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1101 := by
  apply localUnsat_implies_entails f1101 [c52, c152, c1100, c78, c136, c83, c190, c473, c17, c58, c463, c866] c1101 unsat1101 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c473 := h 472 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c463 := h 462 (by decide)
  have h11 : Entails.eval a c866 := h 865 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1102 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨15, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1102 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c52, some c26, some c473, some c381, some c165, some c866, some c13, some c510, some c837, some c614, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1102 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1102 : lratChecker f1102 p1102 = .success := by decide +kernel
theorem unsat1102 : Unsatisfiable (PosFin 31) f1102 := by
  apply lratCheckerSound f1102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1102
  · intro a ha; simp [p1102] at ha; subst a; trivial
  · exact checked1102
theorem derived1102 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1102 := by
  apply localUnsat_implies_entails f1102 [c52, c26, c473, c381, c165, c866, c13, c510, c837, c614] c1102 unsat1102 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c473 := h 472 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c866 := h 865 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c510 := h 509 (by decide)
  have h8 : Entails.eval a c837 := h 836 (by decide)
  have h9 : Entails.eval a c614 := h 613 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1103 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1103 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c52, some c259, some c1102, some c2, some c244, some c292, some c22, some c21, some c812, some c792, some c115, some c469, some c344, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1103 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1103 : lratChecker f1103 p1103 = .success := by decide +kernel
theorem unsat1103 : Unsatisfiable (PosFin 31) f1103 := by
  apply lratCheckerSound f1103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1103
  · intro a ha; simp [p1103] at ha; subst a; trivial
  · exact checked1103
theorem derived1103 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1103 := by
  apply localUnsat_implies_entails f1103 [c52, c259, c1102, c2, c244, c292, c22, c21, c812, c792, c115, c469, c344] c1103 unsat1103 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c1102 := derived1102 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c244 := h 243 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c812 := h 811 (by decide)
  have h9 : Entails.eval a c792 := h 791 (by decide)
  have h10 : Entails.eval a c115 := h 114 (by decide)
  have h11 : Entails.eval a c469 := h 468 (by decide)
  have h12 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1104 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1104 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c52, some c1103, some c58, some c201, some c473, some c2, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1104 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1104 : lratChecker f1104 p1104 = .success := by decide +kernel
theorem unsat1104 : Unsatisfiable (PosFin 31) f1104 := by
  apply lratCheckerSound f1104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1104
  · intro a ha; simp [p1104] at ha; subst a; trivial
  · exact checked1104
theorem derived1104 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1104 := by
  apply localUnsat_implies_entails f1104 [c52, c1103, c58, c201, c473, c2] c1104 unsat1104 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c473 := h 472 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1105 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1105 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1100, some c1082, some c152, some c52, some c1101, some c1104, some c133, some c80, some c187, some c22, some c21, some c635, some c702, some c60, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1105 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1105 : lratChecker f1105 p1105 = .success := by decide +kernel
theorem unsat1105 : Unsatisfiable (PosFin 31) f1105 := by
  apply lratCheckerSound f1105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1105
  · intro a ha; simp [p1105] at ha; subst a; trivial
  · exact checked1105
theorem derived1105 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1105 := by
  apply localUnsat_implies_entails f1105 [c1100, c1082, c152, c52, c1101, c1104, c133, c80, c187, c22, c21, c635, c702, c60] c1105 unsat1105 (by rfl) a
  have h0 : Entails.eval a c1100 := derived1100 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c1101 := derived1101 a h
  have h5 : Entails.eval a c1104 := derived1104 a h
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c187 := h 186 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c635 := h 634 (by decide)
  have h12 : Entails.eval a c702 := h 701 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1106 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1106 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1100, some c80, some c187, some c21, some c72, some c1082, some c635, some c812, some c260, some c171, some c162, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1106 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1106 : lratChecker f1106 p1106 = .success := by decide +kernel
theorem unsat1106 : Unsatisfiable (PosFin 31) f1106 := by
  apply lratCheckerSound f1106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1106
  · intro a ha; simp [p1106] at ha; subst a; trivial
  · exact checked1106
theorem derived1106 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1106 := by
  apply localUnsat_implies_entails f1106 [c1100, c80, c187, c21, c72, c1082, c635, c812, c260, c171, c162] c1106 unsat1106 (by rfl) a
  have h0 : Entails.eval a c1100 := derived1100 a h
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c1082 := derived1082 a h
  have h6 : Entails.eval a c635 := h 634 (by decide)
  have h7 : Entails.eval a c812 := h 811 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c171 := h 170 (by decide)
  have h10 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1107 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1107 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1105, some c1100, some c1082, some c133, some c80, some c187, some c22, some c21, some c72, some c1106, some c608, some c257, some c315, some c705, some c312, some c538, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1107 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1107 : lratChecker f1107 p1107 = .success := by decide +kernel
theorem unsat1107 : Unsatisfiable (PosFin 31) f1107 := by
  apply lratCheckerSound f1107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1107
  · intro a ha; simp [p1107] at ha; subst a; trivial
  · exact checked1107
theorem derived1107 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1107 := by
  apply localUnsat_implies_entails f1107 [c1105, c1100, c1082, c133, c80, c187, c22, c21, c72, c1106, c608, c257, c315, c705, c312, c538] c1107 unsat1107 (by rfl) a
  have h0 : Entails.eval a c1105 := derived1105 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c1106 := derived1106 a h
  have h10 : Entails.eval a c608 := h 607 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  have h12 : Entails.eval a c315 := h 314 (by decide)
  have h13 : Entails.eval a c705 := h 704 (by decide)
  have h14 : Entails.eval a c312 := h 311 (by decide)
  have h15 : Entails.eval a c538 := h 537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1108 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨12, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1108 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c158, some c50, some c22, some c21, some c201, some c307, some c788, some c452, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1108 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1108 : lratChecker f1108 p1108 = .success := by decide +kernel
theorem unsat1108 : Unsatisfiable (PosFin 31) f1108 := by
  apply lratCheckerSound f1108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1108
  · intro a ha; simp [p1108] at ha; subst a; trivial
  · exact checked1108
theorem derived1108 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1108 := by
  apply localUnsat_implies_entails f1108 [c158, c50, c22, c21, c201, c307, c788, c452] c1108 unsat1108 (by rfl) a
  have h0 : Entails.eval a c158 := h 157 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c307 := h 306 (by decide)
  have h6 : Entails.eval a c788 := h 787 (by decide)
  have h7 : Entails.eval a c452 := h 451 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1109 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨15, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1109 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c578, some c120, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p1109 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1109 : lratChecker f1109 p1109 = .success := by decide +kernel
theorem unsat1109 : Unsatisfiable (PosFin 31) f1109 := by
  apply lratCheckerSound f1109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1109
  · intro a ha; simp [p1109] at ha; subst a; trivial
  · exact checked1109
theorem derived1109 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1109 := by
  apply localUnsat_implies_entails f1109 [c578, c120] c1109 unsat1109 (by rfl) a
  have h0 : Entails.eval a c578 := h 577 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1110 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1110 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c158, some c1108, some c3, some c493, some c227, some c1109, some c194, some c642, some c382, some c340, some c497, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1110 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1110 : lratChecker f1110 p1110 = .success := by decide +kernel
theorem unsat1110 : Unsatisfiable (PosFin 31) f1110 := by
  apply lratCheckerSound f1110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1110
  · intro a ha; simp [p1110] at ha; subst a; trivial
  · exact checked1110
theorem derived1110 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1110 := by
  apply localUnsat_implies_entails f1110 [c158, c1108, c3, c493, c227, c1109, c194, c642, c382, c340, c497] c1110 unsat1110 (by rfl) a
  have h0 : Entails.eval a c158 := h 157 (by decide)
  have h1 : Entails.eval a c1108 := derived1108 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c493 := h 492 (by decide)
  have h4 : Entails.eval a c227 := h 226 (by decide)
  have h5 : Entails.eval a c1109 := derived1109 a h
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c642 := h 641 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c340 := h 339 (by decide)
  have h10 : Entails.eval a c497 := h 496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1111 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, false), (⟨28, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1111 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c319, some c26, some c473, some c381, some c493, some c284, some c343, some c307, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1111 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1111 : lratChecker f1111 p1111 = .success := by decide +kernel
theorem unsat1111 : Unsatisfiable (PosFin 31) f1111 := by
  apply lratCheckerSound f1111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1111
  · intro a ha; simp [p1111] at ha; subst a; trivial
  · exact checked1111
theorem derived1111 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1111 := by
  apply localUnsat_implies_entails f1111 [c319, c26, c473, c381, c493, c284, c343, c307] c1111 unsat1111 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c473 := h 472 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  have h4 : Entails.eval a c493 := h 492 (by decide)
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1112 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1112 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1105, some c1100, some c1082, some c1107, some c50, some c1110, some c1111, some c21, some c201, some c635, some c120, some c750, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1112 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1112 : lratChecker f1112 p1112 = .success := by decide +kernel
theorem unsat1112 : Unsatisfiable (PosFin 31) f1112 := by
  apply lratCheckerSound f1112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1112
  · intro a ha; simp [p1112] at ha; subst a; trivial
  · exact checked1112
theorem derived1112 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1112 := by
  apply localUnsat_implies_entails f1112 [c1105, c1100, c1082, c1107, c50, c1110, c1111, c21, c201, c635, c120, c750] c1112 unsat1112 (by rfl) a
  have h0 : Entails.eval a c1105 := derived1105 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c1107 := derived1107 a h
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c1110 := derived1110 a h
  have h6 : Entails.eval a c1111 := derived1111 a h
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c635 := h 634 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1113 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨15, by decide⟩, false), (⟨1, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1113 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c176, some c120, some c315, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1113 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1113 : lratChecker f1113 p1113 = .success := by decide +kernel
theorem unsat1113 : Unsatisfiable (PosFin 31) f1113 := by
  apply lratCheckerSound f1113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1113
  · intro a ha; simp [p1113] at ha; subst a; trivial
  · exact checked1113
theorem derived1113 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1113 := by
  apply localUnsat_implies_entails f1113 [c176, c120, c315] c1113 unsat1113 (by rfl) a
  have h0 : Entails.eval a c176 := h 175 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1114 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨28, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1114 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c50, some c1111, some c201, some c1113, some c194, some c642, some c641, some c614, some c42, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1114 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1114 : lratChecker f1114 p1114 = .success := by decide +kernel
theorem unsat1114 : Unsatisfiable (PosFin 31) f1114 := by
  apply lratCheckerSound f1114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1114
  · intro a ha; simp [p1114] at ha; subst a; trivial
  · exact checked1114
theorem derived1114 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1114 := by
  apply localUnsat_implies_entails f1114 [c50, c1111, c201, c1113, c194, c642, c641, c614, c42] c1114 unsat1114 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c1111 := derived1111 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c1113 := derived1113 a h
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c642 := h 641 (by decide)
  have h6 : Entails.eval a c641 := h 640 (by decide)
  have h7 : Entails.eval a c614 := h 613 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1115 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨28, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1115 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1114, some c50, some c201, some c1113, some c194, some c642, some c644, some c614, some c42, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1115 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1115 : lratChecker f1115 p1115 = .success := by decide +kernel
theorem unsat1115 : Unsatisfiable (PosFin 31) f1115 := by
  apply lratCheckerSound f1115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1115
  · intro a ha; simp [p1115] at ha; subst a; trivial
  · exact checked1115
theorem derived1115 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1115 := by
  apply localUnsat_implies_entails f1115 [c1114, c50, c201, c1113, c194, c642, c644, c614, c42] c1115 unsat1115 (by rfl) a
  have h0 : Entails.eval a c1114 := derived1114 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c1113 := derived1113 a h
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c642 := h 641 (by decide)
  have h6 : Entails.eval a c644 := h 643 (by decide)
  have h7 : Entails.eval a c614 := h 613 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1116 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1116 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1114, some c158, some c1115, some c3, some c493, some c227, some c1109, some c194, some c642, some c340, some c382, some c497, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1116 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1116 : lratChecker f1116 p1116 = .success := by decide +kernel
theorem unsat1116 : Unsatisfiable (PosFin 31) f1116 := by
  apply lratCheckerSound f1116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1116
  · intro a ha; simp [p1116] at ha; subst a; trivial
  · exact checked1116
theorem derived1116 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1116 := by
  apply localUnsat_implies_entails f1116 [c1114, c158, c1115, c3, c493, c227, c1109, c194, c642, c340, c382, c497] c1116 unsat1116 (by rfl) a
  have h0 : Entails.eval a c1114 := derived1114 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c493 := h 492 (by decide)
  have h5 : Entails.eval a c227 := h 226 (by decide)
  have h6 : Entails.eval a c1109 := derived1109 a h
  have h7 : Entails.eval a c194 := h 193 (by decide)
  have h8 : Entails.eval a c642 := h 641 (by decide)
  have h9 : Entails.eval a c340 := h 339 (by decide)
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c497 := h 496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1116

end CochromaticTwenty.Certificates.Z12Direct_5_8_12
