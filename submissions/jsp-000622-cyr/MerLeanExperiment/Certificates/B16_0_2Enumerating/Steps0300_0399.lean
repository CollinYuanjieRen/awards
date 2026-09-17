import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps0200_0299

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c714 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨17, by decide⟩, true), (⟨45, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨47, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c121, some c123, some c713, some c234, some c172, some c134, some c169, some c315, some c368, some c699, some c295, some c319, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c122, c121, c123, c713, c234, c172, c134, c169, c315, c368, c699, c295, c319] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c713 := derived713 a h
  have h4 : Entails.eval a c234 := h 233 (by decide)
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c368 := h 367 (by decide)
  have h10 : Entails.eval a c699 := derived699 a h
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c318, some c148, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c319, c318, c148] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c711, some c120, some c709, some c211, some c712, some c242, some c261, some c714, some c198, some c702, some c715, some c295, some c701, some c148, some c145, some c315, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c711, c120, c709, c211, c712, c242, c261, c714, c198, c702, c715, c295, c701, c148, c145, c315] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c711 := derived711 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c709 := derived709 a h
  have h3 : Entails.eval a c211 := h 210 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c714 := derived714 a h
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c702 := derived702 a h
  have h10 : Entails.eval a c715 := derived715 a h
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c701 := derived701 a h
  have h13 : Entails.eval a c148 := h 147 (by decide)
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c711, some c716, some c215, some c715, some c211, some c706, some c239, some c291, some c368, some c286, some c312, some c148, some c145, some c316, some c445, some c152, some c371, some c198, some c169, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c120, c711, c716, c215, c715, c211, c706, c239, c291, c368, c286, c312, c148, c145, c316, c445, c152, c371, c198, c169] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c711 := derived711 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c715 := derived715 a h
  have h5 : Entails.eval a c211 := h 210 (by decide)
  have h6 : Entails.eval a c706 := derived706 a h
  have h7 : Entails.eval a c239 := h 238 (by decide)
  have h8 : Entails.eval a c291 := h 290 (by decide)
  have h9 : Entails.eval a c368 := h 367 (by decide)
  have h10 : Entails.eval a c286 := h 285 (by decide)
  have h11 : Entails.eval a c312 := h 311 (by decide)
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c145 := h 144 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c445 := derived445 a h
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c371 := h 370 (by decide)
  have h18 : Entails.eval a c198 := h 197 (by decide)
  have h19 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c139, some c145, some c119, some c316, some c239, some c152, some c290, some c291, some c198, some c371, some c368, some c169, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c139, c145, c119, c316, c239, c152, c290, c291, c198, c371, c368, c169] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c139 := h 138 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c239 := h 238 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c368 := h 367 (by decide)
  have h11 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c291, some c286, some c368, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c239, c291, c286, c368] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c291 := h 290 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c173, some c180, some c198, some c142, some c141, some c203, some c445, some c124, some c233, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c173, c180, c198, c142, c141, c203, c445, c124, c233] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c173 := h 172 (by decide)
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c445 := derived445 a h
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c211, some c717, some c120, some c268, some c719, some c173, some c720, some c371, some c291, some c233, some c2, some c124, some c81, some c83, some c203, some c14, some c142, some c198, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c211, c717, c120, c268, c719, c173, c720, c371, c291, c233, c2, c124, c81, c83, c203, c14, c142, c198] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c211 := h 210 (by decide)
  have h1 : Entails.eval a c717 := derived717 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c719 := derived719 a h
  have h5 : Entails.eval a c173 := h 172 (by decide)
  have h6 : Entails.eval a c720 := derived720 a h
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c291 := h 290 (by decide)
  have h9 : Entails.eval a c233 := h 232 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c203 := h 202 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c142 := h 141 (by decide)
  have h17 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c233, some c291, some c286, some c371, some c455, some c445, some c198, some c141, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c233, c291, c286, c371, c455, c445, c198, c141] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c233 := h 232 (by decide)
  have h1 : Entails.eval a c291 := h 290 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c455 := derived455 a h
  have h5 : Entails.eval a c445 := derived445 a h
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨30, by decide⟩, true), (⟨47, by decide⟩, false), (⟨42, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c286, some c133, some c373, some c198, some c172, some c146, some c203, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c286, c133, c373, c198, c172, c146, c203] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c286 := h 285 (by decide)
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨47, by decide⟩, false), (⟨10, by decide⟩, true), (⟨42, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c366, some c172, some c203, some c142, some c146, some c198, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c723, c366, c172, c203, c142, c146, c198] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c211, some c717, some c120, some c718, some c312, some c721, some c125, some c722, some c173, some c134, some c316, some c724, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c211, c717, c120, c718, c312, c721, c125, c722, c173, c134, c316, c724] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c211 := h 210 (by decide)
  have h1 : Entails.eval a c717 := derived717 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c718 := derived718 a h
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c721 := derived721 a h
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c722 := derived722 a h
  have h8 : Entails.eval a c173 := h 172 (by decide)
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c316 := h 315 (by decide)
  have h11 : Entails.eval a c724 := derived724 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c717, some c120, some c211, some c725, some c213, some c267, some c264, some c125, some c124, some c203, some c135, some c239, some c237, some c139, some c173, some c293, some c312, some c371, some c142, some c180, some c198, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c717, c120, c211, c725, c213, c267, c264, c125, c124, c203, c135, c239, c237, c139, c173, c293, c312, c371, c142, c180, c198] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c717 := derived717 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c725 := derived725 a h
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c239 := h 238 (by decide)
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c173 := h 172 (by decide)
  have h15 : Entails.eval a c293 := h 292 (by decide)
  have h16 : Entails.eval a c312 := h 311 (by decide)
  have h17 : Entails.eval a c371 := h 370 (by decide)
  have h18 : Entails.eval a c142 := h 141 (by decide)
  have h19 : Entails.eval a c180 := h 179 (by decide)
  have h20 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨25, by decide⟩, true), (⟨23, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c133, some c231, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c113, c133, c231] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨42, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨47, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c268, some c264, some c2, some c124, some c45, some c203, some c174, some c14, some c83, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c239, c268, c264, c2, c124, c45, c203, c174, c14, c83] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c174 := h 173 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c45, some c47, some c3, some c35, some c20, some c203, some c107, some c124, some c30, some c261, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c2, c45, c47, c3, c35, c20, c203, c107, c124, c30, c261] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨25, by decide⟩, true), (⟨47, by decide⟩, false), (⟨28, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c287, some c368, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c293, c287, c368] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c287 := h 286 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨47, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c728, some c234, some c729, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c728, c234, c729] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c728 := derived728 a h
  have h1 : Entails.eval a c234 := h 233 (by decide)
  have h2 : Entails.eval a c729 := derived729 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c729, some c45, some c47, some c268, some c14, some c124, some c203, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c2, c729, c45, c47, c268, c14, c124, c203] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨30, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨47, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c732, some c264, some c265, some c126, some c203, some c172, some c130, some c242, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c731, c732, c264, c265, c126, c203, c172, c130, c242] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c732 := derived732 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c130 := h 129 (by decide)
  have h8 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c726, some c318, some c213, some c319, some c119, some c145, some c139, some c717, some c120, some c727, some c198, some c152, some c730, some c733, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c726, c318, c213, c319, c119, c145, c139, c717, c120, c727, c198, c152, c730, c733] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c726 := derived726 a h
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c213 := h 212 (by decide)
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c717 := derived717 a h
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c727 := derived727 a h
  have h10 : Entails.eval a c198 := h 197 (by decide)
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c730 := derived730 a h
  have h13 : Entails.eval a c733 := derived733 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨25, by decide⟩, false), (⟨20, by decide⟩, false), (⟨31, by decide⟩, true), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c145, some c152, some c732, some c264, some c265, some c126, some c6, some c203, some c42, some c47, some c130, some c13, some c12, some c261, some c112, some c30, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c119, c145, c152, c732, c264, c265, c126, c6, c203, c42, c47, c130, c13, c12, c261, c112, c30] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c732 := derived732 a h
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c130 := h 129 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨47, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c121, some c45, some c261, some c231, some c124, some c203, some c3, some c170, some c239, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c2, c121, c45, c261, c231, c124, c203, c3, c170, c239] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c231 := h 230 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c35, some c34, some c110, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c45, c35, c34, c110] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c717, some c120, some c726, some c319, some c318, some c139, some c145, some c119, some c213, some c734, some c735, some c198, some c736, some c264, some c265, some c737, some c13, some c9, some c105, some c107, some c12, some c39, some c203, some c261, some c684, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c717, c120, c726, c319, c318, c139, c145, c119, c213, c734, c735, c198, c736, c264, c265, c737, c13, c9, c105, c107, c12, c39, c203, c261, c684] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c717 := derived717 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c726 := derived726 a h
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c213 := h 212 (by decide)
  have h9 : Entails.eval a c734 := derived734 a h
  have h10 : Entails.eval a c735 := derived735 a h
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c736 := derived736 a h
  have h13 : Entails.eval a c264 := h 263 (by decide)
  have h14 : Entails.eval a c265 := h 264 (by decide)
  have h15 : Entails.eval a c737 := derived737 a h
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c9 := h 8 (by decide)
  have h18 : Entails.eval a c105 := h 104 (by decide)
  have h19 : Entails.eval a c107 := h 106 (by decide)
  have h20 : Entails.eval a c12 := h 11 (by decide)
  have h21 : Entails.eval a c39 := h 38 (by decide)
  have h22 : Entails.eval a c203 := h 202 (by decide)
  have h23 : Entails.eval a c261 := h 260 (by decide)
  have h24 : Entails.eval a c684 := derived684 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c738, some c215, some c717, some c120, some c139, some c145, some c119, some c578, some c268, some c261, some c203, some c211, some c3, some c684, some c315, some c45, some c213, some c2, some c265, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c738, c215, c717, c120, c139, c145, c119, c578, c268, c261, c203, c211, c3, c684, c315, c45, c213, c2, c265] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c738 := derived738 a h
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c717 := derived717 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c578 := derived578 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c211 := h 210 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c684 := derived684 a h
  have h14 : Entails.eval a c315 := h 314 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c213 := h 212 (by decide)
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c738, some c215, some c315, some c213, some c267, some c739, some c120, some c737, some c13, some c620, some c51, some c107, some c9, some c30, some c198, some c261, some c132, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c738, c215, c315, c213, c267, c739, c120, c737, c13, c620, c51, c107, c9, c30, c198, c261, c132] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c738 := derived738 a h
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c739 := derived739 a h
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c737 := derived737 a h
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c620 := derived620 a h
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c198 := h 197 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c738, some c215, some c120, some c315, some c213, some c267, some c740, some c265, some c125, some c2, some c261, some c45, some c30, some c121, some c35, some c106, some c198, some c107, some c20, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c738, c215, c120, c315, c213, c267, c740, c265, c125, c2, c261, c45, c30, c121, c35, c106, c198, c107, c20] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c738 := derived738 a h
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c740 := derived740 a h
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c106 := h 105 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c107 := h 106 (by decide)
  have h18 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c265, some c3, some c684, some c51, some c261, some c7, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c267, c265, c3, c684, c51, c261, c7] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c684 := derived684 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨28, by decide⟩, false), (⟨20, by decide⟩, true), (⟨11, by decide⟩, true), (⟨27, by decide⟩, false), (⟨31, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c51, some c49, some c7, some c24, some c261, some c277, some c589, some c223, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c3, c51, c49, c7, c24, c261, c277, c589, c223] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  have h7 : Entails.eval a c589 := derived589 a h
  have h8 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨43, by decide⟩, true), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨42, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c174, some c235, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c132, c174, c235] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c174 := h 173 (by decide)
  have h2 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c739, some c738, some c215, some c717, some c120, some c741, some c134, some c114, some c144, some c203, some c742, some c213, some c743, some c268, some c233, some c7, some c51, some c744, some c198, some c141, some c43, some c10, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c739, c738, c215, c717, c120, c741, c134, c114, c144, c203, c742, c213, c743, c268, c233, c7, c51, c744, c198, c141, c43, c10] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c739 := derived739 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c717 := derived717 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c741 := derived741 a h
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c742 := derived742 a h
  have h11 : Entails.eval a c213 := h 212 (by decide)
  have h12 : Entails.eval a c743 := derived743 a h
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c233 := h 232 (by decide)
  have h15 : Entails.eval a c7 := h 6 (by decide)
  have h16 : Entails.eval a c51 := h 50 (by decide)
  have h17 : Entails.eval a c744 := derived744 a h
  have h18 : Entails.eval a c198 := h 197 (by decide)
  have h19 : Entails.eval a c141 := h 140 (by decide)
  have h20 : Entails.eval a c43 := h 42 (by decide)
  have h21 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c738, some c215, some c745, some c211, some c267, some c213, some c268, some c125, some c120, some c135, some c469, some c233, some c173, some c134, some c368, some c316, some c169, some c146, some c198, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c738, c215, c745, c211, c267, c213, c268, c125, c120, c135, c469, c233, c173, c134, c368, c316, c169, c146, c198] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c738 := derived738 a h
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c211 := h 210 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  have h10 : Entails.eval a c469 := derived469 a h
  have h11 : Entails.eval a c233 := h 232 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c146 := h 145 (by decide)
  have h18 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c717, some c738, some c215, some c745, some c211, some c267, some c213, some c746, some c203, some c137, some c144, some c238, some c316, some c291, some c445, some c150, some c371, some c367, some c198, some c169, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c120, c717, c738, c215, c745, c211, c267, c213, c746, c203, c137, c144, c238, c316, c291, c445, c150, c371, c367, c198, c169] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c717 := derived717 a h
  have h2 : Entails.eval a c738 := derived738 a h
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c745 := derived745 a h
  have h5 : Entails.eval a c211 := h 210 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c746 := derived746 a h
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c137 := h 136 (by decide)
  have h11 : Entails.eval a c144 := h 143 (by decide)
  have h12 : Entails.eval a c238 := h 237 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c445 := derived445 a h
  have h16 : Entails.eval a c150 := h 149 (by decide)
  have h17 : Entails.eval a c371 := h 370 (by decide)
  have h18 : Entails.eval a c367 := h 366 (by decide)
  have h19 : Entails.eval a c198 := h 197 (by decide)
  have h20 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨43, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c173, some c169, some c366, some c368, some c172, some c291, some c295, some c203, some c715, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c173, c169, c366, c368, c172, c291, c295, c203, c715] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c173 := h 172 (by decide)
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c295 := h 294 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c715 := derived715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c715, some c319, some c203, some c139, some c119, some c268, some c263, some c727, some c5, some c1, some c41, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c715, c319, c203, c139, c119, c268, c263, c727, c5, c1, c41] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c715 := derived715 a h
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c727 := derived727 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨21, by decide⟩, false), (⟨45, by decide⟩, false), (⟨12, by decide⟩, false), (⟨42, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c203, some c12, some c82, some c24, some c161, some c330, some c59, some c61, some c254, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c267, c203, c12, c82, c24, c161, c330, c59, c61, c254] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c161 := h 160 (by decide)
  have h6 : Entails.eval a c330 := h 329 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, false), (⟨42, by decide⟩, false), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c749, some c203, some c137, some c117, some c268, some c267, some c119, some c7, some c125, some c51, some c266, some c236, some c293, some c750, some c105, some c88, some c1, some c24, some c229, some c161, some c165, some c133, some c66, some c228, some c271, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c747, c749, c203, c137, c117, c268, c267, c119, c7, c125, c51, c266, c236, c293, c750, c105, c88, c1, c24, c229, c161, c165, c133, c66, c228, c271] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c749 := derived749 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c236 := h 235 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c750 := derived750 a h
  have h15 : Entails.eval a c105 := h 104 (by decide)
  have h16 : Entails.eval a c88 := h 87 (by decide)
  have h17 : Entails.eval a c1 := h 0 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c229 := h 228 (by decide)
  have h20 : Entails.eval a c161 := h 160 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c133 := h 132 (by decide)
  have h23 : Entails.eval a c66 := h 65 (by decide)
  have h24 : Entails.eval a c228 := h 227 (by decide)
  have h25 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨42, by decide⟩, false), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c315, some c751, some c706, some c136, some c263, some c710, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c747, c315, c751, c706, c136, c263, c710] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c751 := derived751 a h
  have h3 : Entails.eval a c706 := derived706 a h
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c710 := derived710 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c125, some c121, some c263, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 57) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c125, c121, c263] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c125 := h 124 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c753, some c233, some c752, some c236, some c291, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 57) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c747, c753, c233, c752, c236, c291] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c752 := derived752 a h
  have h4 : Entails.eval a c236 := h 235 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c753, some c264, some c173, some c169, some c748, some c366, some c239, some c172, some c128, some c203, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 57) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c747, c753, c264, c173, c169, c748, c366, c239, c172, c128, c203] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c173 := h 172 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c748 := derived748 a h
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c239 := h 238 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c753, some c266, some c264, some c755, some c233, some c236, some c754, some c291, some c132, some c315, some c749, some c268, some c116, some c117, some c203, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 57) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c747, c753, c266, c264, c755, c233, c236, c754, c291, c132, c315, c749, c268, c116, c117, c203] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c755 := derived755 a h
  have h5 : Entails.eval a c233 := h 232 (by decide)
  have h6 : Entails.eval a c236 := h 235 (by decide)
  have h7 : Entails.eval a c754 := derived754 a h
  have h8 : Entails.eval a c291 := h 290 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c749 := derived749 a h
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c117 := h 116 (by decide)
  have h15 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c130, some c124, some c266, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 57) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c130, c124, c266] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c130 := h 129 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c264, some c118, some c116, some c316, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 57) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c266, c264, c118, c116, c316] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c6, some c47, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 57) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c118, c6, c47] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c757, some c203, some c702, some c705, some c116, some c136, some c370, some c82, some c180, some c700, some c291, some c319, some c51, some c295, some c90, some c25, some c162, some c330, some c59, some c60, some c253, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 57) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c747, c757, c203, c702, c705, c116, c136, c370, c82, c180, c700, c291, c319, c51, c295, c90, c25, c162, c330, c59, c60, c253] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c702 := derived702 a h
  have h4 : Entails.eval a c705 := derived705 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c700 := derived700 a h
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c295 := h 294 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c330 := h 329 (by decide)
  have h19 : Entails.eval a c59 := h 58 (by decide)
  have h20 : Entails.eval a c60 := h 59 (by decide)
  have h21 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨43, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c445, some c291, some c371, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 57) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c315, c445, c291, c371] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c445 := derived445 a h
  have h2 : Entails.eval a c291 := h 290 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨43, by decide⟩, true), (⟨42, by decide⟩, false), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c761, some c747, some c759, some c760, some c266, some c268, some c125, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 57) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c761, c747, c759, c760, c266, c268, c125] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c761 := derived761 a h
  have h1 : Entails.eval a c747 := derived747 a h
  have h2 : Entails.eval a c759 := derived759 a h
  have h3 : Entails.eval a c760 := derived760 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c758, some c132, some c203, some c268, some c130, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 57) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c266, c758, c132, c203, c268, c130] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c758 := derived758 a h
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c763, some c125, some c268, some c757, some c203, some c2, some c762, some c239, some c369, some c176, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 57) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c747, c763, c125, c268, c757, c203, c2, c762, c239, c369, c176] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c757 := derived757 a h
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c762 := derived762 a h
  have h8 : Entails.eval a c239 := h 238 (by decide)
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c756, some c198, some c763, some c125, some c2, some c268, some c263, some c759, some c757, some c203, some c764, some c702, some c173, some c700, some c239, some c291, some c315, some c715, some c45, some c116, some c136, some c295, some c241, some c90, some c138, some c25, some c47, some c162, some c153, some c70, some c217, some c275, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 57) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c747, c756, c198, c763, c125, c2, c268, c263, c759, c757, c203, c764, c702, c173, c700, c239, c291, c315, c715, c45, c116, c136, c295, c241, c90, c138, c25, c47, c162, c153, c70, c217, c275] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c756 := derived756 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c763 := derived763 a h
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c759 := derived759 a h
  have h9 : Entails.eval a c757 := derived757 a h
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c764 := derived764 a h
  have h12 : Entails.eval a c702 := derived702 a h
  have h13 : Entails.eval a c173 := h 172 (by decide)
  have h14 : Entails.eval a c700 := derived700 a h
  have h15 : Entails.eval a c239 := h 238 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c315 := h 314 (by decide)
  have h18 : Entails.eval a c715 := derived715 a h
  have h19 : Entails.eval a c45 := h 44 (by decide)
  have h20 : Entails.eval a c116 := h 115 (by decide)
  have h21 : Entails.eval a c136 := h 135 (by decide)
  have h22 : Entails.eval a c295 := h 294 (by decide)
  have h23 : Entails.eval a c241 := h 240 (by decide)
  have h24 : Entails.eval a c90 := h 89 (by decide)
  have h25 : Entails.eval a c138 := h 137 (by decide)
  have h26 : Entails.eval a c25 := h 24 (by decide)
  have h27 : Entails.eval a c47 := h 46 (by decide)
  have h28 : Entails.eval a c162 := h 161 (by decide)
  have h29 : Entails.eval a c153 := h 152 (by decide)
  have h30 : Entails.eval a c70 := h 69 (by decide)
  have h31 : Entails.eval a c217 := h 216 (by decide)
  have h32 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c765, some c145, some c134, some c114, some c266, some c264, some c233, some c236, some c291, some c319, some c144, some c203, some c706, some c709, some c116, some c4, some c263, some c214, some c53, some c123, some c6, some c198, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 57) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c747, c765, c145, c134, c114, c266, c264, c233, c236, c291, c319, c144, c203, c706, c709, c116, c4, c263, c214, c53, c123, c6, c198] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c765 := derived765 a h
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c233 := h 232 (by decide)
  have h8 : Entails.eval a c236 := h 235 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c319 := h 318 (by decide)
  have h11 : Entails.eval a c144 := h 143 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c706 := derived706 a h
  have h14 : Entails.eval a c709 := derived709 a h
  have h15 : Entails.eval a c116 := h 115 (by decide)
  have h16 : Entails.eval a c4 := h 3 (by decide)
  have h17 : Entails.eval a c263 := h 262 (by decide)
  have h18 : Entails.eval a c214 := h 213 (by decide)
  have h19 : Entails.eval a c53 := h 52 (by decide)
  have h20 : Entails.eval a c123 := h 122 (by decide)
  have h21 : Entails.eval a c6 := h 5 (by decide)
  have h22 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨22, by decide⟩, true), (⟨9, by decide⟩, true), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c263, some c214, some c1, some c77, some c42, some c38, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 57) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c268, c263, c214, c1, c77, c42, c38] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c214 := h 213 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c753, some c266, some c145, some c134, some c141, some c233, some c236, some c312, some c135, some c170, some c295, some c767, some c7, some c51, some c43, some c10, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 57) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c747, c753, c266, c145, c134, c141, c233, c236, c312, c135, c170, c295, c767, c7, c51, c43, c10] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c312 := h 311 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c767 := derived767 a h
  have h13 : Entails.eval a c7 := h 6 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c43 := h 42 (by decide)
  have h16 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c198, some c753, some c264, some c128, some c7, some c119, some c766, some c768, some c266, some c135, some c170, some c315, some c319, some c51, some c10, some c43, some c79, some c105, some c107, some c113, some c173, some c232, some c293, some c295, some c370, some c229, some c214, some c117, some c25, some c38, some c164, some c320, some c47, some c224, some c24, some c353, some c59, some c71, some c306, some c249, some c167, some c365, some c96, some c58, some c195, some c193, some c336, some c386, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 57) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c747, c198, c753, c264, c128, c7, c119, c766, c768, c266, c135, c170, c315, c319, c51, c10, c43, c79, c105, c107, c113, c173, c232, c293, c295, c370, c229, c214, c117, c25, c38, c164, c320, c47, c224, c24, c353, c59, c71, c306, c249, c167, c365, c96, c58, c195, c193, c336, c386] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c128 := h 127 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c766 := derived766 a h
  have h8 : Entails.eval a c768 := derived768 a h
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c315 := h 314 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c43 := h 42 (by decide)
  have h17 : Entails.eval a c79 := h 78 (by decide)
  have h18 : Entails.eval a c105 := h 104 (by decide)
  have h19 : Entails.eval a c107 := h 106 (by decide)
  have h20 : Entails.eval a c113 := h 112 (by decide)
  have h21 : Entails.eval a c173 := h 172 (by decide)
  have h22 : Entails.eval a c232 := h 231 (by decide)
  have h23 : Entails.eval a c293 := h 292 (by decide)
  have h24 : Entails.eval a c295 := h 294 (by decide)
  have h25 : Entails.eval a c370 := h 369 (by decide)
  have h26 : Entails.eval a c229 := h 228 (by decide)
  have h27 : Entails.eval a c214 := h 213 (by decide)
  have h28 : Entails.eval a c117 := h 116 (by decide)
  have h29 : Entails.eval a c25 := h 24 (by decide)
  have h30 : Entails.eval a c38 := h 37 (by decide)
  have h31 : Entails.eval a c164 := h 163 (by decide)
  have h32 : Entails.eval a c320 := h 319 (by decide)
  have h33 : Entails.eval a c47 := h 46 (by decide)
  have h34 : Entails.eval a c224 := h 223 (by decide)
  have h35 : Entails.eval a c24 := h 23 (by decide)
  have h36 : Entails.eval a c353 := h 352 (by decide)
  have h37 : Entails.eval a c59 := h 58 (by decide)
  have h38 : Entails.eval a c71 := h 70 (by decide)
  have h39 : Entails.eval a c306 := h 305 (by decide)
  have h40 : Entails.eval a c249 := h 248 (by decide)
  have h41 : Entails.eval a c167 := h 166 (by decide)
  have h42 : Entails.eval a c365 := h 364 (by decide)
  have h43 : Entails.eval a c96 := h 95 (by decide)
  have h44 : Entails.eval a c58 := h 57 (by decide)
  have h45 : Entails.eval a c195 := h 194 (by decide)
  have h46 : Entails.eval a c193 := h 192 (by decide)
  have h47 : Entails.eval a c336 := h 335 (by decide)
  have h48 : Entails.eval a c386 := h 385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c198, some c753, some c766, some c7, some c769, some c233, some c173, some c169, some c79, some c87, some c10, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 57) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c747, c198, c753, c766, c7, c769, c233, c173, c169, c79, c87, c10] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c766 := derived766 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c769 := derived769 a h
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c173 := h 172 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c87 := h 86 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c233, some c173, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 57) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c239, c233, c173] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c233 := h 232 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c263, some c173, some c244, some c366, some c295, some c172, some c41, some c25, some c164, some c269, some c219, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 57) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c747, c263, c173, c244, c366, c295, c172, c41, c25, c164, c269, c219] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c244 := h 243 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c79, some c295, some c13, some c41, some c82, some c5, some c25, some c24, some c164, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 57) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c366, c79, c295, c13, c41, c82, c5, c25, c24, c164] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c766, some c747, some c198, some c753, some c266, some c264, some c768, some c770, some c268, some c263, some c123, some c1, some c113, some c771, some c135, some c170, some c315, some c772, some c236, some c293, some c773, some c139, some c312, some c295, some c767, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 57) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c766, c747, c198, c753, c266, c264, c768, c770, c268, c263, c123, c1, c113, c771, c135, c170, c315, c772, c236, c293, c773, c139, c312, c295, c767] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c747 := derived747 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c768 := derived768 a h
  have h7 : Entails.eval a c770 := derived770 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c771 := derived771 a h
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c170 := h 169 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  have h17 : Entails.eval a c772 := derived772 a h
  have h18 : Entails.eval a c236 := h 235 (by decide)
  have h19 : Entails.eval a c293 := h 292 (by decide)
  have h20 : Entails.eval a c773 := derived773 a h
  have h21 : Entails.eval a c139 := h 138 (by decide)
  have h22 : Entails.eval a c312 := h 311 (by decide)
  have h23 : Entails.eval a c295 := h 294 (by decide)
  have h24 : Entails.eval a c767 := derived767 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c774, some c766, some c747, some c753, some c768, some c266, some c132, some c118, some c6, some c759, some c263, some c9, some c113, some c42, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 57) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c774, c766, c747, c753, c768, c266, c132, c118, c6, c759, c263, c9, c113, c42] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c774 := derived774 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c747 := derived747 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c768 := derived768 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c759 := derived759 a h
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨30, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c53, some c4, some c24, some c164, some c281, some c226, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 57) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c53, c4, c24, c164, c281, c226] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c281 := h 280 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨9, by decide⟩, false), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c264, some c118, some c6, some c776, some c207, some c42, some c21, some c153, some c270, some c226, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 57) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c266, c264, c118, c6, c776, c207, c42, c21, c153, c270, c226] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c776 := derived776 a h
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c135, some c239, some c81, some c173, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 57) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c45, c135, c239, c81, c173] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c239 := h 238 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c775, some c766, some c747, some c774, some c268, some c263, some c757, some c777, some c114, some c2, some c778, some c14, some c110, some c47, some c146, some c315, some c759, some c138, some c243, some c293, some c241, some c116, some c109, some c24, some c164, some c220, some c273, some c71, some c156, some c59, some c301, some c152, some c306, some c25, some c331, some c31, some c83, some c173, some c312, some c295, some c372, some c366, some c43, some c63, some c100, some c354, some c192, some c184, some c343, some c387, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 57) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c775, c766, c747, c774, c268, c263, c757, c777, c114, c2, c778, c14, c110, c47, c146, c315, c759, c138, c243, c293, c241, c116, c109, c24, c164, c220, c273, c71, c156, c59, c301, c152, c306, c25, c331, c31, c83, c173, c312, c295, c372, c366, c43, c63, c100, c354, c192, c184, c343, c387] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c775 := derived775 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c747 := derived747 a h
  have h3 : Entails.eval a c774 := derived774 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c757 := derived757 a h
  have h7 : Entails.eval a c777 := derived777 a h
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c778 := derived778 a h
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c315 := h 314 (by decide)
  have h16 : Entails.eval a c759 := derived759 a h
  have h17 : Entails.eval a c138 := h 137 (by decide)
  have h18 : Entails.eval a c243 := h 242 (by decide)
  have h19 : Entails.eval a c293 := h 292 (by decide)
  have h20 : Entails.eval a c241 := h 240 (by decide)
  have h21 : Entails.eval a c116 := h 115 (by decide)
  have h22 : Entails.eval a c109 := h 108 (by decide)
  have h23 : Entails.eval a c24 := h 23 (by decide)
  have h24 : Entails.eval a c164 := h 163 (by decide)
  have h25 : Entails.eval a c220 := h 219 (by decide)
  have h26 : Entails.eval a c273 := h 272 (by decide)
  have h27 : Entails.eval a c71 := h 70 (by decide)
  have h28 : Entails.eval a c156 := h 155 (by decide)
  have h29 : Entails.eval a c59 := h 58 (by decide)
  have h30 : Entails.eval a c301 := h 300 (by decide)
  have h31 : Entails.eval a c152 := h 151 (by decide)
  have h32 : Entails.eval a c306 := h 305 (by decide)
  have h33 : Entails.eval a c25 := h 24 (by decide)
  have h34 : Entails.eval a c331 := h 330 (by decide)
  have h35 : Entails.eval a c31 := h 30 (by decide)
  have h36 : Entails.eval a c83 := h 82 (by decide)
  have h37 : Entails.eval a c173 := h 172 (by decide)
  have h38 : Entails.eval a c312 := h 311 (by decide)
  have h39 : Entails.eval a c295 := h 294 (by decide)
  have h40 : Entails.eval a c372 := h 371 (by decide)
  have h41 : Entails.eval a c366 := h 365 (by decide)
  have h42 : Entails.eval a c43 := h 42 (by decide)
  have h43 : Entails.eval a c63 := h 62 (by decide)
  have h44 : Entails.eval a c100 := h 99 (by decide)
  have h45 : Entails.eval a c354 := h 353 (by decide)
  have h46 : Entails.eval a c192 := h 191 (by decide)
  have h47 : Entails.eval a c184 := h 183 (by decide)
  have h48 : Entails.eval a c343 := h 342 (by decide)
  have h49 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c775, some c774, some c766, some c747, some c268, some c263, some c757, some c777, some c114, some c2, some c759, some c778, some c14, some c47, some c146, some c138, some c315, some c243, some c293, some c241, some c779, some c207, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 57) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c775, c774, c766, c747, c268, c263, c757, c777, c114, c2, c759, c778, c14, c47, c146, c138, c315, c243, c293, c241, c779, c207] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c775 := derived775 a h
  have h1 : Entails.eval a c774 := derived774 a h
  have h2 : Entails.eval a c766 := derived766 a h
  have h3 : Entails.eval a c747 := derived747 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c757 := derived757 a h
  have h7 : Entails.eval a c777 := derived777 a h
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c759 := derived759 a h
  have h11 : Entails.eval a c778 := derived778 a h
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c138 := h 137 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  have h17 : Entails.eval a c243 := h 242 (by decide)
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c241 := h 240 (by decide)
  have h20 : Entails.eval a c779 := derived779 a h
  have h21 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c774, some c780, some c125, some c132, some c266, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 57) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c747, c774, c780, c125, c132, c266] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c774 := derived774 a h
  have h2 : Entails.eval a c780 := derived780 a h
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c15, some c51, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 57) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c147, c15, c51] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c781, some c140, some c747, some c119, some c7, some c125, some c706, some c236, some c173, some c92, some c782, some c203, some c151, some c19, some c54, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 57) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c781, c140, c747, c119, c7, c125, c706, c236, c173, c92, c782, c203, c151, c19, c54] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c781 := derived781 a h
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c747 := derived747 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c706 := derived706 a h
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c173 := h 172 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c782 := derived782 a h
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c151 := h 150 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c784 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c176, some c17, some c82, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 57) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c176, c17, c82] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c176 := h 175 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c781, some c140, some c783, some c268, some c244, some c173, some c236, some c114, some c2, some c124, some c84, some c784, some c203, some c15, some c778, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 57) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c747, c781, c140, c783, c268, c244, c173, c236, c114, c2, c124, c84, c784, c203, c15, c778] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c781 := derived781 a h
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c783 := derived783 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c244 := h 243 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c784 := derived784 a h
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c778 := derived778 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c15, some c45, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 57) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c115, c15, c45] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c263, some c785, some c140, some c244, some c139, some c173, some c236, some c114, some c2, some c84, some c784, some c786, some c203, some c151, some c319, some c312, some c206, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 57) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c747, c263, c785, c140, c244, c139, c173, c236, c114, c2, c84, c784, c786, c203, c151, c319, c312, c206] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c785 := derived785 a h
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c244 := h 243 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c784 := derived784 a h
  have h12 : Entails.eval a c786 := derived786 a h
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c319 := h 318 (by decide)
  have h16 : Entails.eval a c312 := h 311 (by decide)
  have h17 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨16, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c244, some c173, some c236, some c371, some c121, some c180, some c198, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 57) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c263, c244, c173, c236, c371, c121, c180, c198] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c244 := h 243 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c236 := h 235 (by decide)
  have h4 : Entails.eval a c371 := h 370 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨42, by decide⟩, false), (⟨14, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨48, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c83, some c370, some c20, some c293, some c315, some c316, some c761, some c206, some c152, some c81, some c43, some c30, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 57) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c83, c370, c20, c293, c315, c316, c761, c206, c152, c81, c43, c30] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c83 := h 82 (by decide)
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c761 := derived761 a h
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨48, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c789, some c138, some c316, some c47, some c293, some c20, some c369, some c291, some c45, some c23, some c30, some c273, some c107, some c105, some c217, some c18, some c156, some c153, some c75, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 57) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c198, c789, c138, c316, c47, c293, c20, c369, c291, c45, c23, c30, c273, c107, c105, c217, c18, c156, c153, c75] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c789 := derived789 a h
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c291 := h 290 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c273 := h 272 (by decide)
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c105 := h 104 (by decide)
  have h15 : Entails.eval a c217 := h 216 (by decide)
  have h16 : Entails.eval a c18 := h 17 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c153 := h 152 (by decide)
  have h19 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c45, some c23, some c30, some c273, some c107, some c105, some c217, some c18, some c156, some c153, some c75, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 57) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c198, c45, c23, c30, c273, c107, c105, c217, c18, c156, c153, c75] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c217 := h 216 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c156 := h 155 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c785, some c747, some c263, some c787, some c788, some c114, some c2, some c121, some c790, some c173, some c198, some c316, some c47, some c293, some c20, some c791, some c206, some c291, some c87, some c372, some c30, some c172, some c43, some c705, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 57) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c785, c747, c263, c787, c788, c114, c2, c121, c790, c173, c198, c316, c47, c293, c20, c791, c206, c291, c87, c372, c30, c172, c43, c705] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c785 := derived785 a h
  have h1 : Entails.eval a c747 := derived747 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c787 := derived787 a h
  have h4 : Entails.eval a c788 := derived788 a h
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c790 := derived790 a h
  have h9 : Entails.eval a c173 := h 172 (by decide)
  have h10 : Entails.eval a c198 := h 197 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c791 := derived791 a h
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c291 := h 290 (by decide)
  have h18 : Entails.eval a c87 := h 86 (by decide)
  have h19 : Entails.eval a c372 := h 371 (by decide)
  have h20 : Entails.eval a c30 := h 29 (by decide)
  have h21 : Entails.eval a c172 := h 171 (by decide)
  have h22 : Entails.eval a c43 := h 42 (by decide)
  have h23 : Entails.eval a c705 := derived705 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨46, by decide⟩, false), (⟨31, by decide⟩, false), (⟨47, by decide⟩, false), (⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨48, by decide⟩, true), (⟨23, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c319, some c293, some c578, some c241, some c203, some c116, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 57) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c315, c319, c293, c578, c241, c203, c116] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c293 := h 292 (by decide)
  have h3 : Entails.eval a c578 := derived578 a h
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c794 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c787, some c788, some c263, some c785, some c114, some c2, some c121, some c198, some c759, some c790, some c173, some c792, some c152, some c138, some c793, some c206, some c291, some c312, some c373, some c295, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 57) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c747, c787, c788, c263, c785, c114, c2, c121, c198, c759, c790, c173, c792, c152, c138, c793, c206, c291, c312, c373, c295] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c787 := derived787 a h
  have h2 : Entails.eval a c788 := derived788 a h
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c785 := derived785 a h
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c759 := derived759 a h
  have h10 : Entails.eval a c790 := derived790 a h
  have h11 : Entails.eval a c173 := h 172 (by decide)
  have h12 : Entails.eval a c792 := derived792 a h
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c138 := h 137 (by decide)
  have h15 : Entails.eval a c793 := derived793 a h
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c291 := h 290 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c373 := h 372 (by decide)
  have h20 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c291, some c312, some c373, some c295, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 57) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c206, c291, c312, c373, c295] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c291 := h 290 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c794, some c266, some c6, some c787, some c788, some c263, some c785, some c759, some c145, some c134, some c83, some c180, some c795, some c319, some c144, some c295, some c203, some c242, some c702, some c51, some c90, some c23, some c25, some c162, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 57) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c747, c794, c266, c6, c787, c788, c263, c785, c759, c145, c134, c83, c180, c795, c319, c144, c295, c203, c242, c702, c51, c90, c23, c25, c162] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c794 := derived794 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c787 := derived787 a h
  have h5 : Entails.eval a c788 := derived788 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c785 := derived785 a h
  have h8 : Entails.eval a c759 := derived759 a h
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c180 := h 179 (by decide)
  have h13 : Entails.eval a c795 := derived795 a h
  have h14 : Entails.eval a c319 := h 318 (by decide)
  have h15 : Entails.eval a c144 := h 143 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c203 := h 202 (by decide)
  have h18 : Entails.eval a c242 := h 241 (by decide)
  have h19 : Entails.eval a c702 := derived702 a h
  have h20 : Entails.eval a c51 := h 50 (by decide)
  have h21 : Entails.eval a c90 := h 89 (by decide)
  have h22 : Entails.eval a c23 := h 22 (by decide)
  have h23 : Entails.eval a c25 := h 24 (by decide)
  have h24 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨31, by decide⟩, false), (⟨26, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨30, by decide⟩, false), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c51, some c144, some c23, some c30, some c162, some c42, some c106, some c105, some c61, some c68, some c75, some c113, some c25, some c181, some c349, some c156, some c336, some c219, some c256, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 57) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c319, c51, c144, c23, c30, c162, c42, c106, c105, c61, c68, c75, c113, c25, c181, c349, c156, c336, c219, c256] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c144 := h 143 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c181 := h 180 (by decide)
  have h15 : Entails.eval a c349 := h 348 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  have h17 : Entails.eval a c336 := h 335 (by decide)
  have h18 : Entails.eval a c219 := h 218 (by decide)
  have h19 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c796, some c13, some c747, some c794, some c266, some c6, some c118, some c787, some c788, some c263, some c785, some c145, some c134, some c797, some c206, some c291, some c795, some c312, some c369, some c144, some c176, some c203, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 57) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c796, c13, c747, c794, c266, c6, c118, c787, c788, c263, c785, c145, c134, c797, c206, c291, c795, c312, c369, c144, c176, c203] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c747 := derived747 a h
  have h3 : Entails.eval a c794 := derived794 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c787 := derived787 a h
  have h8 : Entails.eval a c788 := derived788 a h
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c785 := derived785 a h
  have h11 : Entails.eval a c145 := h 144 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c797 := derived797 a h
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c291 := h 290 (by decide)
  have h16 : Entails.eval a c795 := derived795 a h
  have h17 : Entails.eval a c312 := h 311 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  have h19 : Entails.eval a c144 := h 143 (by decide)
  have h20 : Entails.eval a c176 := h 175 (by decide)
  have h21 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨30, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c787, some c788, some c263, some c785, some c206, some c291, some c42, some c369, some c30, some c173, some c87, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c747, c787, c788, c263, c785, c206, c291, c42, c369, c30, c173, c87] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c787 := derived787 a h
  have h2 : Entails.eval a c788 := derived788 a h
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c785 := derived785 a h
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c173 := h 172 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c51, some c12, some c699, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c112, c51, c12, c699] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c699 := derived699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c794, some c266, some c787, some c788, some c263, some c785, some c118, some c6, some c796, some c13, some c798, some c316, some c293, some c799, some c800, some c23, some c30, some c273, some c105, some c68, some c12, some c162, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c747, c794, c266, c787, c788, c263, c785, c118, c6, c796, c13, c798, c316, c293, c799, c800, c23, c30, c273, c105, c68, c12, c162] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c794 := derived794 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c787 := derived787 a h
  have h4 : Entails.eval a c788 := derived788 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c785 := derived785 a h
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c796 := derived796 a h
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c798 := derived798 a h
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c799 := derived799 a h
  have h15 : Entails.eval a c800 := derived800 a h
  have h16 : Entails.eval a c23 := h 22 (by decide)
  have h17 : Entails.eval a c30 := h 29 (by decide)
  have h18 : Entails.eval a c273 := h 272 (by decide)
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c68 := h 67 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c105, some c43, some c12, some c145, some c699, some c315, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c13, c105, c43, c12, c145, c699, c315] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c699 := derived699 a h
  have h6 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨48, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c785, some c43, some c139, some c145, some c79, some c315, some c45, some c169, some c293, some c148, some c23, some c234, some c82, some c161, some c24, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c802, c785, c43, c139, c145, c79, c315, c45, c169, c293, c148, c23, c234, c82, c161, c24] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c785 := derived785 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  have h9 : Entails.eval a c293 := h 292 (by decide)
  have h10 : Entails.eval a c148 := h 147 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c234 := h 233 (by decide)
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c266, some c785, some c23, some c34, some c109, some c16, some c161, some c72, some c24, some c279, some c234, some c139, some c748, some c329, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c747, c266, c785, c23, c34, c109, c16, c161, c72, c24, c279, c234, c139, c748, c329] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c785 := derived785 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c161 := h 160 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c279 := h 278 (by decide)
  have h11 : Entails.eval a c234 := h 233 (by decide)
  have h12 : Entails.eval a c139 := h 138 (by decide)
  have h13 : Entails.eval a c748 := derived748 a h
  have h14 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c108, some c145, some c16, some c312, some c203, some c144, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c45, c108, c145, c16, c312, c203, c144] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨48, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c266, some c785, some c802, some c803, some c805, some c34, some c804, some c109, some c293, some c16, some c315, some c318, some c203, some c144, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c747, c266, c785, c802, c803, c805, c34, c804, c109, c293, c16, c315, c318, c203, c144] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c785 := derived785 a h
  have h3 : Entails.eval a c802 := derived802 a h
  have h4 : Entails.eval a c803 := derived803 a h
  have h5 : Entails.eval a c805 := derived805 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c804 := derived804 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c293 := h 292 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c315 := h 314 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨35, by decide⟩, false), (⟨38, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨43, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c81, some c173, some c329, some c87, some c72, some c604, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c108, c81, c173, c329, c87, c72, c604] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c604 := derived604 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c787, some c788, some c263, some c785, some c794, some c266, some c801, some c198, some c1, some c113, some c806, some c210, some c291, some c42, some c34, some c26, some c270, some c218, some c807, some c13, some c43, some c87, some c139, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c747, c787, c788, c263, c785, c794, c266, c801, c198, c1, c113, c806, c210, c291, c42, c34, c26, c270, c218, c807, c13, c43, c87, c139] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c787 := derived787 a h
  have h2 : Entails.eval a c788 := derived788 a h
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c785 := derived785 a h
  have h5 : Entails.eval a c794 := derived794 a h
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c801 := derived801 a h
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c806 := derived806 a h
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  have h14 : Entails.eval a c42 := h 41 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c26 := h 25 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c218 := h 217 (by decide)
  have h19 : Entails.eval a c807 := derived807 a h
  have h20 : Entails.eval a c13 := h 12 (by decide)
  have h21 : Entails.eval a c43 := h 42 (by decide)
  have h22 : Entails.eval a c87 := h 86 (by decide)
  have h23 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c785, some c747, some c263, some c787, some c808, some c115, some c3, some c684, some c266, some c114, some c2, some c45, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c785, c747, c263, c787, c808, c115, c3, c684, c266, c114, c2, c45] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c785 := derived785 a h
  have h1 : Entails.eval a c747 := derived747 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c787 := derived787 a h
  have h4 : Entails.eval a c808 := derived808 a h
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c684 := derived684 a h
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c17, some c203, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c151, c17, c203] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, false), (⟨35, by decide⟩, false), (⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨24, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c279, some c319, some c110, some c109, some c810, some c167, some c64, some c73, some c252, some c352, some c349, some c338, some c306, some c675, some c676, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c279, c319, c110, c109, c810, c167, c64, c73, c252, c352, c349, c338, c306, c675, c676] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c279 := h 278 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c810 := derived810 a h
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c349 := h 348 (by decide)
  have h11 : Entails.eval a c338 := h 337 (by decide)
  have h12 : Entails.eval a c306 := h 305 (by decide)
  have h13 : Entails.eval a c675 := derived675 a h
  have h14 : Entails.eval a c676 := derived676 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨2, by decide⟩, true), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨11, by decide⟩, false), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c167, some c9, some c107, some c105, some c12, some c75, some c162, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c198, c167, c9, c107, c105, c12, c75, c162] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c809, some c747, some c125, some c266, some c132, some c7, some c119, some c785, some c319, some c51, some c3, some c23, some c34, some c279, some c228, some c811, some c812, some c140, some c151, some c236, some c203, some c134, some c149, some c315, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c809, c747, c125, c266, c132, c7, c119, c785, c319, c51, c3, c23, c34, c279, c228, c811, c812, c140, c151, c236, c203, c134, c149, c315] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c809 := derived809 a h
  have h1 : Entails.eval a c747 := derived747 a h
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c785 := derived785 a h
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c279 := h 278 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c811 := derived811 a h
  have h16 : Entails.eval a c812 := derived812 a h
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c236 := h 235 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c134 := h 133 (by decide)
  have h22 : Entails.eval a c149 := h 148 (by decide)
  have h23 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived813

end CochromaticTwenty.Certificates.B16_0_2Enumerating
