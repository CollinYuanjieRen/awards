import MerLeanExperiment.Certificates.B16_8_0Enumerating.Steps0200_0299

/-! Generated from the actual pinned b16_8_0-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_0Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c719 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c289, some c590, some c441, some c67, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c289, c590, c441, c67] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c289 := h 288 (by decide)
  have h1 : Entails.eval a c590 := derived590 a h
  have h2 : Entails.eval a c441 := derived441 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c705, some c380, some c546, some c665, some c702, some c86, some c103, some c66, some c35, some c54, some c719, some c670, some c286, some c710, some c37, some c206, some c339, some c32, some c207, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c718, c705, c380, c546, c665, c702, c86, c103, c66, c35, c54, c719, c670, c286, c710, c37, c206, c339, c32, c207] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c702 := derived702 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c719 := derived719 a h
  have h12 : Entails.eval a c670 := derived670 a h
  have h13 : Entails.eval a c286 := h 285 (by decide)
  have h14 : Entails.eval a c710 := derived710 a h
  have h15 : Entails.eval a c37 := h 36 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c339 := h 338 (by decide)
  have h18 : Entails.eval a c32 := h 31 (by decide)
  have h19 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c705, some c380, some c546, some c665, some c702, some c86, some c103, some c720, some c333, some c717, some c670, some c330, some c59, some c37, some c295, some c286, some c707, some c211, some c212, some c31, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c718, c705, c380, c546, c665, c702, c86, c103, c720, c333, c717, c670, c330, c59, c37, c295, c286, c707, c211, c212, c31] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c702 := derived702 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c720 := derived720 a h
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c717 := derived717 a h
  have h11 : Entails.eval a c670 := derived670 a h
  have h12 : Entails.eval a c330 := h 329 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  have h16 : Entails.eval a c286 := h 285 (by decide)
  have h17 : Entails.eval a c707 := derived707 a h
  have h18 : Entails.eval a c211 := h 210 (by decide)
  have h19 : Entails.eval a c212 := h 211 (by decide)
  have h20 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨14, by decide⟩, false), (⟨12, by decide⟩, true), (⟨34, by decide⟩, true), (⟨44, by decide⟩, false), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c192, some c208, some c124, some c223, some c109, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c192, c208, c124, c223, c109] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c223 := h 222 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c161, some c109, some c229, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c161, c109, c229] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c161 := h 160 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c718, some c705, some c380, some c665, some c702, some c86, some c103, some c333, some c717, some c670, some c330, some c37, some c286, some c295, some c707, some c212, some c238, some c196, some c33, some c721, some c66, some c104, some c31, some c68, some c594, some c58, some c195, some c368, some c373, some c36, some c365, some c151, some c273, some c274, some c15, some c14, some c142, some c122, some c173, some c722, some c134, some c156, some c328, some c225, some c267, some c723, some c124, some c202, some c229, some c389, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c546, c718, c705, c380, c665, c702, c86, c103, c333, c717, c670, c330, c37, c286, c295, c707, c212, c238, c196, c33, c721, c66, c104, c31, c68, c594, c58, c195, c368, c373, c36, c365, c151, c273, c274, c15, c14, c142, c122, c173, c722, c134, c156, c328, c225, c267, c723, c124, c202, c229, c389] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c718 := derived718 a h
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c702 := derived702 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c717 := derived717 a h
  have h10 : Entails.eval a c670 := derived670 a h
  have h11 : Entails.eval a c330 := h 329 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c286 := h 285 (by decide)
  have h14 : Entails.eval a c295 := h 294 (by decide)
  have h15 : Entails.eval a c707 := derived707 a h
  have h16 : Entails.eval a c212 := h 211 (by decide)
  have h17 : Entails.eval a c238 := h 237 (by decide)
  have h18 : Entails.eval a c196 := h 195 (by decide)
  have h19 : Entails.eval a c33 := h 32 (by decide)
  have h20 : Entails.eval a c721 := derived721 a h
  have h21 : Entails.eval a c66 := h 65 (by decide)
  have h22 : Entails.eval a c104 := h 103 (by decide)
  have h23 : Entails.eval a c31 := h 30 (by decide)
  have h24 : Entails.eval a c68 := h 67 (by decide)
  have h25 : Entails.eval a c594 := derived594 a h
  have h26 : Entails.eval a c58 := h 57 (by decide)
  have h27 : Entails.eval a c195 := h 194 (by decide)
  have h28 : Entails.eval a c368 := h 367 (by decide)
  have h29 : Entails.eval a c373 := h 372 (by decide)
  have h30 : Entails.eval a c36 := h 35 (by decide)
  have h31 : Entails.eval a c365 := h 364 (by decide)
  have h32 : Entails.eval a c151 := h 150 (by decide)
  have h33 : Entails.eval a c273 := h 272 (by decide)
  have h34 : Entails.eval a c274 := h 273 (by decide)
  have h35 : Entails.eval a c15 := h 14 (by decide)
  have h36 : Entails.eval a c14 := h 13 (by decide)
  have h37 : Entails.eval a c142 := h 141 (by decide)
  have h38 : Entails.eval a c122 := h 121 (by decide)
  have h39 : Entails.eval a c173 := h 172 (by decide)
  have h40 : Entails.eval a c722 := derived722 a h
  have h41 : Entails.eval a c134 := h 133 (by decide)
  have h42 : Entails.eval a c156 := h 155 (by decide)
  have h43 : Entails.eval a c328 := h 327 (by decide)
  have h44 : Entails.eval a c225 := h 224 (by decide)
  have h45 : Entails.eval a c267 := h 266 (by decide)
  have h46 : Entails.eval a c723 := derived723 a h
  have h47 : Entails.eval a c124 := h 123 (by decide)
  have h48 : Entails.eval a c202 := h 201 (by decide)
  have h49 : Entails.eval a c229 := h 228 (by decide)
  have h50 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c721, some c718, some c705, some c380, some c546, some c665, some c702, some c86, some c103, some c66, some c333, some c717, some c670, some c724, some c69, some c569, some c319, some c275, some c36, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c721, c718, c705, c380, c546, c665, c702, c86, c103, c66, c333, c717, c670, c724, c69, c569, c319, c275, c36] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c721 := derived721 a h
  have h1 : Entails.eval a c718 := derived718 a h
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c546 := derived546 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c702 := derived702 a h
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c333 := h 332 (by decide)
  have h11 : Entails.eval a c717 := derived717 a h
  have h12 : Entails.eval a c670 := derived670 a h
  have h13 : Entails.eval a c724 := derived724 a h
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c569 := derived569 a h
  have h16 : Entails.eval a c319 := h 318 (by decide)
  have h17 : Entails.eval a c275 := h 274 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨37, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c569, some c319, some c275, some c36, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c69, c569, c319, c275, c36] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c569 := derived569 a h
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c665, some c702, some c86, some c66, some c103, some c705, some c380, some c718, some c721, some c725, some c35, some c289, some c719, some c670, some c286, some c710, some c37, some c339, some c207, some c34, some c244, some c201, some c726, some c104, some c31, some c68, some c47, some c200, some c368, some c373, some c303, some c365, some c151, some c36, some c15, some c14, some c126, some c317, some c352, some c138, some c173, some c723, some c179, some c568, some c140, some c225, some c192, some c213, some c284, some c229, some c267, some c390, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c546, c665, c702, c86, c66, c103, c705, c380, c718, c721, c725, c35, c289, c719, c670, c286, c710, c37, c339, c207, c34, c244, c201, c726, c104, c31, c68, c47, c200, c368, c373, c303, c365, c151, c36, c15, c14, c126, c317, c352, c138, c173, c723, c179, c568, c140, c225, c192, c213, c284, c229, c267, c390] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c702 := derived702 a h
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c705 := derived705 a h
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c718 := derived718 a h
  have h9 : Entails.eval a c721 := derived721 a h
  have h10 : Entails.eval a c725 := derived725 a h
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c719 := derived719 a h
  have h14 : Entails.eval a c670 := derived670 a h
  have h15 : Entails.eval a c286 := h 285 (by decide)
  have h16 : Entails.eval a c710 := derived710 a h
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c339 := h 338 (by decide)
  have h19 : Entails.eval a c207 := h 206 (by decide)
  have h20 : Entails.eval a c34 := h 33 (by decide)
  have h21 : Entails.eval a c244 := h 243 (by decide)
  have h22 : Entails.eval a c201 := h 200 (by decide)
  have h23 : Entails.eval a c726 := derived726 a h
  have h24 : Entails.eval a c104 := h 103 (by decide)
  have h25 : Entails.eval a c31 := h 30 (by decide)
  have h26 : Entails.eval a c68 := h 67 (by decide)
  have h27 : Entails.eval a c47 := h 46 (by decide)
  have h28 : Entails.eval a c200 := h 199 (by decide)
  have h29 : Entails.eval a c368 := h 367 (by decide)
  have h30 : Entails.eval a c373 := h 372 (by decide)
  have h31 : Entails.eval a c303 := h 302 (by decide)
  have h32 : Entails.eval a c365 := h 364 (by decide)
  have h33 : Entails.eval a c151 := h 150 (by decide)
  have h34 : Entails.eval a c36 := h 35 (by decide)
  have h35 : Entails.eval a c15 := h 14 (by decide)
  have h36 : Entails.eval a c14 := h 13 (by decide)
  have h37 : Entails.eval a c126 := h 125 (by decide)
  have h38 : Entails.eval a c317 := h 316 (by decide)
  have h39 : Entails.eval a c352 := h 351 (by decide)
  have h40 : Entails.eval a c138 := h 137 (by decide)
  have h41 : Entails.eval a c173 := h 172 (by decide)
  have h42 : Entails.eval a c723 := derived723 a h
  have h43 : Entails.eval a c179 := h 178 (by decide)
  have h44 : Entails.eval a c568 := derived568 a h
  have h45 : Entails.eval a c140 := h 139 (by decide)
  have h46 : Entails.eval a c225 := h 224 (by decide)
  have h47 : Entails.eval a c192 := h 191 (by decide)
  have h48 : Entails.eval a c213 := h 212 (by decide)
  have h49 : Entails.eval a c284 := h 283 (by decide)
  have h50 : Entails.eval a c229 := h 228 (by decide)
  have h51 : Entails.eval a c267 := h 266 (by decide)
  have h52 : Entails.eval a c390 := h 389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨48, by decide⟩, false), (⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c352, some c62, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c320, c352, c62] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c368, some c74, some c728, some c36, some c274, some c276, some c51, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c68, c368, c74, c728, c36, c274, c276, c51] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c728 := derived728 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c274 := h 273 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c73, some c374, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c74, c73, c374] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c730, some c268, some c44, some c43, some c309, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c730, c268, c44, c43, c309] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c730 := derived730 a h
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨7, by decide⟩, false), (⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c729, some c104, some c730, some c731, some c36, some c312, some c353, some c55, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c729, c104, c730, c731, c36, c312, c353, c55] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c729 := derived729 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c730 := derived730 a h
  have h3 : Entails.eval a c731 := derived731 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c312 := h 311 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨37, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c730, some c731, some c312, some c36, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c54, c730, c731, c312, c36] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c730 := derived730 a h
  have h2 : Entails.eval a c731 := derived731 a h
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c318, some c320, some c62, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c318, c320, c62] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c318 := h 317 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c368, some c74, some c734, some c36, some c274, some c276, some c51, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c68, c368, c74, c734, c36, c274, c276, c51] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c734 := derived734 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c274 := h 273 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c732, some c104, some c733, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c735, c732, c104, c733] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c732 := derived732 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c733 := derived733 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c736, some c731, some c733, some c36, some c46, some c319, some c571, some c69, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c380, c736, c731, c733, c36, c46, c319, c571, c69] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c736 := derived736 a h
  have h2 : Entails.eval a c731 := derived731 a h
  have h3 : Entails.eval a c733 := derived733 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c319 := h 318 (by decide)
  have h7 : Entails.eval a c571 := derived571 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c64, some c333, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c55, c64, c333] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c736, some c36, some c57, some c333, some c35, some c289, some c268, some c53, some c74, some c276, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c380, c736, c36, c57, c333, c35, c289, c268, c53, c74, c276] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c736 := derived736 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c333 := h 332 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c736, some c738, some c739, some c320, some c74, some c83, some c368, some c371, some c363, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c380, c736, c738, c739, c320, c74, c83, c368, c371, c363] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c736 := derived736 a h
  have h2 : Entails.eval a c738 := derived738 a h
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨7, by decide⟩, true), (⟨41, by decide⟩, false), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c312, some c55, some c35, some c320, some c268, some c83, some c46, some c272, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c312, c55, c35, c320, c268, c83, c46, c272] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c312 := h 311 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c741, some c36, some c57, some c268, some c35, some c44, some c316, some c276, some c83, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c741, c36, c57, c268, c35, c44, c316, c276, c83] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c741 := derived741 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c276 := h 275 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, false), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c276, some c44, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c268, c276, c44] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c276 := h 275 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c740, some c65, some c368, some c742, some c736, some c386, some c543, some c81, some c743, some c36, some c312, some c320, some c55, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c740, c65, c368, c742, c736, c386, c543, c81, c743, c36, c312, c320, c55] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c740 := derived740 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c742 := derived742 a h
  have h4 : Entails.eval a c736 := derived736 a h
  have h5 : Entails.eval a c386 := h 385 (by decide)
  have h6 : Entails.eval a c543 := derived543 a h
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c743 := derived743 a h
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c312 := h 311 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c665, some c546, some c702, some c66, some c727, some c744, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c665, c546, c702, c66, c727, c744] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c665 := derived665 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c702 := derived702 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c727 := derived727 a h
  have h5 : Entails.eval a c744 := derived744 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨37, by decide⟩, true), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c272, some c281, some c257, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c272, c281, c257] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c281 := h 280 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c53, some c46, some c49, some c307, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c53, c46, c49, c307] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨34, by decide⟩, false), (⟨31, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨42, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c368, some c312, some c79, some c371, some c363, some c386, some c365, some c319, some c746, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c367, c368, c312, c79, c371, c363, c386, c365, c319, c746] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c371 := h 370 (by decide)
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c386 := h 385 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c746 := derived746 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c99, some c147, some c4, some c168, some c178, some c173, some c386, some c356, some c175, some c516, some c374, some c184, some c163, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c86, c99, c147, c4, c168, c178, c173, c386, c356, c175, c516, c374, c184, c163] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c386 := h 385 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c175 := h 174 (by decide)
  have h10 : Entails.eval a c516 := derived516 a h
  have h11 : Entails.eval a c374 := h 373 (by decide)
  have h12 : Entails.eval a c184 := h 183 (by decide)
  have h13 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨31, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c368, some c748, some c79, some c77, some c57, some c371, some c316, some c272, some c363, some c187, some c297, some c341, some c20, some c190, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c367, c368, c748, c79, c77, c57, c371, c316, c272, c363, c187, c297, c341, c20, c190] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c748 := derived748 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c297 := h 296 (by decide)
  have h12 : Entails.eval a c341 := h 340 (by decide)
  have h13 : Entails.eval a c20 := h 19 (by decide)
  have h14 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨46, by decide⟩, false), (⟨22, by decide⟩, true), (⟨39, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c283, some c327, some c192, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c283, c327, c192] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c283 := h 282 (by decide)
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c83, some c79, some c372, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c83, c79, c372] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c83 := h 82 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨47, by decide⟩, false), (⟨49, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c97, some c719, some c380, some c36, some c57, some c333, some c187, some c21, some c751, some c363, some c274, some c324, some c38, some c190, some c20, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 57) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c99, c97, c719, c380, c36, c57, c333, c187, c21, c751, c363, c274, c324, c38, c190, c20] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c719 := derived719 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c333 := h 332 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c751 := derived751 a h
  have h10 : Entails.eval a c363 := h 362 (by decide)
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c324 := h 323 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c190 := h 189 (by decide)
  have h15 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c346, some c60, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 57) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c333, c346, c60] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c346 := h 345 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨34, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c64, some c60, some c351, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 57) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c64, c60, c351] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c64 := h 63 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c99, some c97, some c747, some c750, some c749, some c380, some c719, some c752, some c753, some c754, some c187, some c21, some c755, some c751, some c363, some c318, some c280, some c38, some c190, some c20, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 57) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c86, c99, c97, c747, c750, c749, c380, c719, c752, c753, c754, c187, c21, c755, c751, c363, c318, c280, c38, c190, c20] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c747 := derived747 a h
  have h4 : Entails.eval a c750 := derived750 a h
  have h5 : Entails.eval a c749 := derived749 a h
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c719 := derived719 a h
  have h8 : Entails.eval a c752 := derived752 a h
  have h9 : Entails.eval a c753 := derived753 a h
  have h10 : Entails.eval a c754 := derived754 a h
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c755 := derived755 a h
  have h14 : Entails.eval a c751 := derived751 a h
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c318 := h 317 (by decide)
  have h17 : Entails.eval a c280 := h 279 (by decide)
  have h18 : Entails.eval a c38 := h 37 (by decide)
  have h19 : Entails.eval a c190 := h 189 (by decide)
  have h20 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨30, by decide⟩, true), (⟨26, by decide⟩, true), (⟨6, by decide⟩, false), (⟨39, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c719, some c333, some c187, some c21, some c234, some c197, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 57) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c719, c333, c187, c21, c234, c197] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c719 := derived719 a h
  have h1 : Entails.eval a c333 := h 332 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c234 := h 233 (by decide)
  have h5 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c665, some c546, some c745, some c756, some c382, some c67, some c442, some c750, some c752, some c384, some c337, some c317, some c42, some c37, some c293, some c310, some c757, some c147, some c356, some c4, some c319, some c281, some c152, some c266, some c327, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 57) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c665, c546, c745, c756, c382, c67, c442, c750, c752, c384, c337, c317, c42, c37, c293, c310, c757, c147, c356, c4, c319, c281, c152, c266, c327] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c665 := derived665 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c756 := derived756 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c442 := derived442 a h
  have h7 : Entails.eval a c750 := derived750 a h
  have h8 : Entails.eval a c752 := derived752 a h
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c337 := h 336 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c293 := h 292 (by decide)
  have h15 : Entails.eval a c310 := h 309 (by decide)
  have h16 : Entails.eval a c757 := derived757 a h
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c4 := h 3 (by decide)
  have h20 : Entails.eval a c319 := h 318 (by decide)
  have h21 : Entails.eval a c281 := h 280 (by decide)
  have h22 : Entails.eval a c152 := h 151 (by decide)
  have h23 : Entails.eval a c266 := h 265 (by decide)
  have h24 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c665, some c546, some c745, some c756, some c382, some c67, some c442, some c750, some c752, some c384, some c758, some c36, some c753, some c293, some c273, some c147, some c515, some c42, some c37, some c4, some c297, some c341, some c354, some c152, some c264, some c283, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 57) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c665, c546, c745, c756, c382, c67, c442, c750, c752, c384, c758, c36, c753, c293, c273, c147, c515, c42, c37, c4, c297, c341, c354, c152, c264, c283] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c665 := derived665 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c756 := derived756 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c442 := derived442 a h
  have h7 : Entails.eval a c750 := derived750 a h
  have h8 : Entails.eval a c752 := derived752 a h
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c758 := derived758 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c753 := derived753 a h
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c273 := h 272 (by decide)
  have h15 : Entails.eval a c147 := h 146 (by decide)
  have h16 : Entails.eval a c515 := derived515 a h
  have h17 : Entails.eval a c42 := h 41 (by decide)
  have h18 : Entails.eval a c37 := h 36 (by decide)
  have h19 : Entails.eval a c4 := h 3 (by decide)
  have h20 : Entails.eval a c297 := h 296 (by decide)
  have h21 : Entails.eval a c341 := h 340 (by decide)
  have h22 : Entails.eval a c354 := h 353 (by decide)
  have h23 : Entails.eval a c152 := h 151 (by decide)
  have h24 : Entails.eval a c264 := h 263 (by decide)
  have h25 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c665, some c745, some c756, some c382, some c752, some c67, some c442, some c759, some c70, some c283, some c327, some c40, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 57) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c546, c665, c745, c756, c382, c752, c67, c442, c759, c70, c283, c327, c40] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c756 := derived756 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c752 := derived752 a h
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c442 := derived442 a h
  have h8 : Entails.eval a c759 := derived759 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c327 := h 326 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c283, some c327, some c40, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 57) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c283, c327, c40] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c283 := h 282 (by decide)
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c372, some c361, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 57) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c374, c372, c361] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c67, some c433, some c361, some c97, some c516, some c70, some c360, some c371, some c380, some c147, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 57) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c67, c433, c361, c97, c516, c70, c360, c371, c380, c147] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c516 := derived516 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c53, some c46, some c293, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 57) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c53, c46, c293] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c64, some c57, some c337, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 57) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c64, c57, c337] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c64 := h 63 (by decide)
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c665, some c745, some c756, some c382, some c384, some c762, some c83, some c764, some c765, some c760, some c97, some c70, some c761, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 57) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c546, c665, c745, c756, c382, c384, c762, c83, c764, c765, c760, c97, c70, c761] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c756 := derived756 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c384 := h 383 (by decide)
  have h6 : Entails.eval a c762 := derived762 a h
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c764 := derived764 a h
  have h9 : Entails.eval a c765 := derived765 a h
  have h10 : Entails.eval a c760 := derived760 a h
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c761 := derived761 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c745, some c665, some c546, some c756, some c382, some c384, some c762, some c766, some c99, some c98, some c81, some c91, some c368, some c373, some c380, some c356, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 57) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c745, c665, c546, c756, c382, c384, c762, c766, c99, c98, c81, c91, c368, c373, c380, c356] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c745 := derived745 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c756 := derived756 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c384 := h 383 (by decide)
  have h6 : Entails.eval a c762 := derived762 a h
  have h7 : Entails.eval a c766 := derived766 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c373 := h 372 (by decide)
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨49, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c361, some c356, some c367, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 57) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c361, c356, c367] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c361 := h 360 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨46, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c762, some c367, some c371, some c67, some c433, some c149, some c166, some c11, some c14, some c165, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 57) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c762, c367, c371, c67, c433, c149, c166, c11, c14, c165] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c433 := derived433 a h
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨49, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c175, some c676, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 57) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c175, c676] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c175 := h 174 (by decide)
  have h1 : Entails.eval a c676 := derived676 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c771 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨52, by decide⟩, false), (⟨46, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c327, some c341, some c61, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 57) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c327, c341, c61] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c327 := h 326 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c56, some c335, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 57) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c61, c56, c335] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨35, by decide⟩, true), (⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c335, some c142, some c36, some c481, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 57) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c335, c142, c36, c481] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c335 := h 334 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c481 := derived481 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c767, some c745, some c665, some c546, some c99, some c98, some c86, some c70, some c91, some c382, some c384, some c380, some c762, some c93, some c768, some c373, some c769, some c147, some c5, some c433, some c770, some c15, some c165, some c163, some c771, some c772, some c321, some c773, some c38, some c297, some c291, some c263, some c45, some c277, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 57) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c767, c745, c665, c546, c99, c98, c86, c70, c91, c382, c384, c380, c762, c93, c768, c373, c769, c147, c5, c433, c770, c15, c165, c163, c771, c772, c321, c773, c38, c297, c291, c263, c45, c277] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c767 := derived767 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c762 := derived762 a h
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c768 := derived768 a h
  have h15 : Entails.eval a c373 := h 372 (by decide)
  have h16 : Entails.eval a c769 := derived769 a h
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c5 := h 4 (by decide)
  have h19 : Entails.eval a c433 := derived433 a h
  have h20 : Entails.eval a c770 := derived770 a h
  have h21 : Entails.eval a c15 := h 14 (by decide)
  have h22 : Entails.eval a c165 := h 164 (by decide)
  have h23 : Entails.eval a c163 := h 162 (by decide)
  have h24 : Entails.eval a c771 := derived771 a h
  have h25 : Entails.eval a c772 := derived772 a h
  have h26 : Entails.eval a c321 := h 320 (by decide)
  have h27 : Entails.eval a c773 := derived773 a h
  have h28 : Entails.eval a c38 := h 37 (by decide)
  have h29 : Entails.eval a c297 := h 296 (by decide)
  have h30 : Entails.eval a c291 := h 290 (by decide)
  have h31 : Entails.eval a c263 := h 262 (by decide)
  have h32 : Entails.eval a c45 := h 44 (by decide)
  have h33 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c386, some c380, some c774, some c767, some c665, some c546, some c86, some c70, some c93, some c382, some c768, some c770, some c762, some c516, some c15, some c163, some c12, some c186, some c772, some c165, some c687, some c327, some c57, some c41, some c319, some c281, some c191, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 57) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c386, c380, c774, c767, c665, c546, c86, c70, c93, c382, c768, c770, c762, c516, c15, c163, c12, c186, c772, c165, c687, c327, c57, c41, c319, c281, c191] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c386 := h 385 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c774 := derived774 a h
  have h3 : Entails.eval a c767 := derived767 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c546 := derived546 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c768 := derived768 a h
  have h11 : Entails.eval a c770 := derived770 a h
  have h12 : Entails.eval a c762 := derived762 a h
  have h13 : Entails.eval a c516 := derived516 a h
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c163 := h 162 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c186 := h 185 (by decide)
  have h18 : Entails.eval a c772 := derived772 a h
  have h19 : Entails.eval a c165 := h 164 (by decide)
  have h20 : Entails.eval a c687 := derived687 a h
  have h21 : Entails.eval a c327 := h 326 (by decide)
  have h22 : Entails.eval a c57 := h 56 (by decide)
  have h23 : Entails.eval a c41 := h 40 (by decide)
  have h24 : Entails.eval a c319 := h 318 (by decide)
  have h25 : Entails.eval a c281 := h 280 (by decide)
  have h26 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c745, some c775, some c97, some c380, some c774, some c665, some c546, some c465, some c67, some c77, some c382, some c368, some c749, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 57) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c745, c775, c97, c380, c774, c665, c546, c465, c67, c77, c382, c368, c749] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c745 := derived745 a h
  have h1 : Entails.eval a c775 := derived775 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c774 := derived774 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c546 := derived546 a h
  have h7 : Entails.eval a c465 := derived465 a h
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c749 := derived749 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c750, some c79, some c41, some c46, some c371, some c316, some c268, some c365, some c325, some c275, some c257, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 57) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c367, c750, c79, c41, c46, c371, c316, c268, c365, c325, c275, c257] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c371 := h 370 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c365 := h 364 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c275 := h 274 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c774, some c767, some c745, some c665, some c546, some c380, some c386, some c775, some c97, some c776, some c777, some c749, some c147, some c356, some c382, some c3, some c516, some c374, some c770, some c89, some c163, some c15, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 57) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c774, c767, c745, c665, c546, c380, c386, c775, c97, c776, c777, c749, c147, c356, c382, c3, c516, c374, c770, c89, c163, c15] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c774 := derived774 a h
  have h1 : Entails.eval a c767 := derived767 a h
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c546 := derived546 a h
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c386 := h 385 (by decide)
  have h7 : Entails.eval a c775 := derived775 a h
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c776 := derived776 a h
  have h10 : Entails.eval a c777 := derived777 a h
  have h11 : Entails.eval a c749 := derived749 a h
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c516 := derived516 a h
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c770 := derived770 a h
  have h19 : Entails.eval a c89 := h 88 (by decide)
  have h20 : Entails.eval a c163 := h 162 (by decide)
  have h21 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨41, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c3, some c175, some c156, some c17, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 57) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c12, c3, c175, c156, c17] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c175 := h 174 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨41, by decide⟩, true), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c173, some c170, some c568, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 57) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c173, c170, c568] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c173 := h 172 (by decide)
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c568 := derived568 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨41, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c175, some c171, some c568, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 57) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c175, c171, c568] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c175 := h 174 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c568 := derived568 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c89, some c97, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 57) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c93, c89, c97] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c778, some c745, some c546, some c382, some c384, some c762, some c444, some c780, some c781, some c782, some c12, some c91, some c88, some c97, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 57) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c778, c745, c546, c382, c384, c762, c444, c780, c781, c782, c12, c91, c88, c97] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c778 := derived778 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  have h5 : Entails.eval a c762 := derived762 a h
  have h6 : Entails.eval a c444 := derived444 a h
  have h7 : Entails.eval a c780 := derived780 a h
  have h8 : Entails.eval a c781 := derived781 a h
  have h9 : Entails.eval a c782 := derived782 a h
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c784 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨23, by decide⟩, true), (⟨13, by decide⟩, false), (⟨41, by decide⟩, true), (⟨50, by decide⟩, true), (⟨42, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c186, some c183, some c111, some c115, some c168, some c108, some c568, some c225, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 57) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c186, c183, c111, c115, c168, c108, c568, c225] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c186 := h 185 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c568 := derived568 a h
  have h7 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨22, by decide⟩, true), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c324, some c751, some c38, some c46, some c274, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 57) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c324, c751, c38, c46, c274] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c324 := h 323 (by decide)
  have h1 : Entails.eval a c751 := derived751 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c785, some c57, some c41, some c318, some c280, some c38, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 57) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c785, c57, c41, c318, c280, c38] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c785 := derived785 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c97, some c777, some c749, some c719, some c88, some c68, some c589, some c373, some c187, some c365, some c151, some c69, some c238, some c235, some c21, some c15, some c784, some c173, some c4, some c156, some c372, some c79, some c786, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 57) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c86, c97, c777, c749, c719, c88, c68, c589, c373, c187, c365, c151, c69, c238, c235, c21, c15, c784, c173, c4, c156, c372, c79, c786] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c777 := derived777 a h
  have h3 : Entails.eval a c749 := derived749 a h
  have h4 : Entails.eval a c719 := derived719 a h
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c589 := derived589 a h
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c365 := h 364 (by decide)
  have h11 : Entails.eval a c151 := h 150 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c238 := h 237 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c784 := derived784 a h
  have h18 : Entails.eval a c173 := h 172 (by decide)
  have h19 : Entails.eval a c4 := h 3 (by decide)
  have h20 : Entails.eval a c156 := h 155 (by decide)
  have h21 : Entails.eval a c372 := h 371 (by decide)
  have h22 : Entails.eval a c79 := h 78 (by decide)
  have h23 : Entails.eval a c786 := derived786 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨20, by decide⟩, true), (⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c41, some c318, some c280, some c190, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 57) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c57, c41, c318, c280, c190] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨53, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c719, some c777, some c373, some c365, some c151, some c69, some c15, some c12, some c173, some c4, some c156, some c372, some c762, some c79, some c589, some c187, some c20, some c21, some c788, some c324, some c327, some c213, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 57) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c97, c719, c777, c373, c365, c151, c69, c15, c12, c173, c4, c156, c372, c762, c79, c589, c187, c20, c21, c788, c324, c327, c213] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c719 := derived719 a h
  have h2 : Entails.eval a c777 := derived777 a h
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c173 := h 172 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c762 := derived762 a h
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c589 := derived589 a h
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c20 := h 19 (by decide)
  have h18 : Entails.eval a c21 := h 20 (by decide)
  have h19 : Entails.eval a c788 := derived788 a h
  have h20 : Entails.eval a c324 := h 323 (by decide)
  have h21 : Entails.eval a c327 := h 326 (by decide)
  have h22 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, false), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨47, by decide⟩, false), (⟨46, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c751, some c327, some c49, some c213, some c295, some c355, some c258, some c205, some c215, some c339, some c32, some c59, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 57) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c751, c327, c49, c213, c295, c355, c258, c205, c215, c339, c32, c59] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c751 := derived751 a h
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c215 := h 214 (by decide)
  have h9 : Entails.eval a c339 := h 338 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨17, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c665, some c783, some c86, some c745, some c21, some c767, some c774, some c778, some c787, some c20, some c97, some c777, some c749, some c238, some c789, some c363, some c719, some c589, some c790, some c41, some c60, some c283, some c339, some c202, some c713, some c258, some c311, some c295, some c204, some c48, some c32, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 57) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c546, c665, c783, c86, c745, c21, c767, c774, c778, c787, c20, c97, c777, c749, c238, c789, c363, c719, c589, c790, c41, c60, c283, c339, c202, c713, c258, c311, c295, c204, c48, c32] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c783 := derived783 a h
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c745 := derived745 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c767 := derived767 a h
  have h7 : Entails.eval a c774 := derived774 a h
  have h8 : Entails.eval a c778 := derived778 a h
  have h9 : Entails.eval a c787 := derived787 a h
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c777 := derived777 a h
  have h13 : Entails.eval a c749 := derived749 a h
  have h14 : Entails.eval a c238 := h 237 (by decide)
  have h15 : Entails.eval a c789 := derived789 a h
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c719 := derived719 a h
  have h18 : Entails.eval a c589 := derived589 a h
  have h19 : Entails.eval a c790 := derived790 a h
  have h20 : Entails.eval a c41 := h 40 (by decide)
  have h21 : Entails.eval a c60 := h 59 (by decide)
  have h22 : Entails.eval a c283 := h 282 (by decide)
  have h23 : Entails.eval a c339 := h 338 (by decide)
  have h24 : Entails.eval a c202 := h 201 (by decide)
  have h25 : Entails.eval a c713 := derived713 a h
  have h26 : Entails.eval a c258 := h 257 (by decide)
  have h27 : Entails.eval a c311 := h 310 (by decide)
  have h28 : Entails.eval a c295 := h 294 (by decide)
  have h29 : Entails.eval a c204 := h 203 (by decide)
  have h30 : Entails.eval a c48 := h 47 (by decide)
  have h31 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c762, some c89, some c779, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 57) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c97, c762, c89, c779] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c779 := derived779 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c745, some c546, some c665, some c783, some c86, some c97, some c778, some c774, some c767, some c777, some c749, some c719, some c787, some c789, some c150, some c3, some c792, some c589, some c187, some c791, some c79, some c372, some c156, some c17, some c168, some c175, some c183, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 57) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c745, c546, c665, c783, c86, c97, c778, c774, c767, c777, c749, c719, c787, c789, c150, c3, c792, c589, c187, c791, c79, c372, c156, c17, c168, c175, c183] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c745 := derived745 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c783 := derived783 a h
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c778 := derived778 a h
  have h7 : Entails.eval a c774 := derived774 a h
  have h8 : Entails.eval a c767 := derived767 a h
  have h9 : Entails.eval a c777 := derived777 a h
  have h10 : Entails.eval a c749 := derived749 a h
  have h11 : Entails.eval a c719 := derived719 a h
  have h12 : Entails.eval a c787 := derived787 a h
  have h13 : Entails.eval a c789 := derived789 a h
  have h14 : Entails.eval a c150 := h 149 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c792 := derived792 a h
  have h17 : Entails.eval a c589 := derived589 a h
  have h18 : Entails.eval a c187 := h 186 (by decide)
  have h19 : Entails.eval a c791 := derived791 a h
  have h20 : Entails.eval a c79 := h 78 (by decide)
  have h21 : Entails.eval a c372 := h 371 (by decide)
  have h22 : Entails.eval a c156 := h 155 (by decide)
  have h23 : Entails.eval a c17 := h 16 (by decide)
  have h24 : Entails.eval a c168 := h 167 (by decide)
  have h25 : Entails.eval a c175 := h 174 (by decide)
  have h26 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c794 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c97, some c367, some c442, some c441, some c749, some c333, some c342, some c289, some c298, some c257, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 57) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c86, c97, c367, c442, c441, c749, c333, c342, c289, c298, c257] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c442 := derived442 a h
  have h4 : Entails.eval a c441 := derived441 a h
  have h5 : Entails.eval a c749 := derived749 a h
  have h6 : Entails.eval a c333 := h 332 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c745, some c546, some c665, some c783, some c86, some c97, some c774, some c793, some c794, some c67, some c719, some c589, some c187, some c235, some c238, some c257, some c298, some c299, some c258, some c205, some c339, some c248, some c211, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 57) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c745, c546, c665, c783, c86, c97, c774, c793, c794, c67, c719, c589, c187, c235, c238, c257, c298, c299, c258, c205, c339, c248, c211] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c745 := derived745 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c783 := derived783 a h
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c774 := derived774 a h
  have h7 : Entails.eval a c793 := derived793 a h
  have h8 : Entails.eval a c794 := derived794 a h
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c719 := derived719 a h
  have h11 : Entails.eval a c589 := derived589 a h
  have h12 : Entails.eval a c187 := h 186 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c238 := h 237 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c298 := h 297 (by decide)
  have h17 : Entails.eval a c299 := h 298 (by decide)
  have h18 : Entails.eval a c258 := h 257 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c339 := h 338 (by decide)
  have h21 : Entails.eval a c248 := h 247 (by decide)
  have h22 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c745, some c546, some c665, some c783, some c86, some c97, some c774, some c793, some c794, some c67, some c719, some c589, some c187, some c235, some c795, some c343, some c342, some c713, some c258, some c248, some c295, some c299, some c200, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 57) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c745, c546, c665, c783, c86, c97, c774, c793, c794, c67, c719, c589, c187, c235, c795, c343, c342, c713, c258, c248, c295, c299, c200] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c745 := derived745 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c783 := derived783 a h
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c774 := derived774 a h
  have h7 : Entails.eval a c793 := derived793 a h
  have h8 : Entails.eval a c794 := derived794 a h
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c719 := derived719 a h
  have h11 : Entails.eval a c589 := derived589 a h
  have h12 : Entails.eval a c187 := h 186 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c795 := derived795 a h
  have h15 : Entails.eval a c343 := h 342 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c713 := derived713 a h
  have h18 : Entails.eval a c258 := h 257 (by decide)
  have h19 : Entails.eval a c248 := h 247 (by decide)
  have h20 : Entails.eval a c295 := h 294 (by decide)
  have h21 : Entails.eval a c299 := h 298 (by decide)
  have h22 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c745, some c665, some c546, some c774, some c778, some c783, some c86, some c97, some c793, some c794, some c79, some c796, some c749, some c368, some c371, some c363, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 57) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c745, c665, c546, c774, c778, c783, c86, c97, c793, c794, c79, c796, c749, c368, c371, c363] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c745 := derived745 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c774 := derived774 a h
  have h4 : Entails.eval a c778 := derived778 a h
  have h5 : Entails.eval a c783 := derived783 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c793 := derived793 a h
  have h9 : Entails.eval a c794 := derived794 a h
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c796 := derived796 a h
  have h12 : Entails.eval a c749 := derived749 a h
  have h13 : Entails.eval a c368 := h 367 (by decide)
  have h14 : Entails.eval a c371 := h 370 (by decide)
  have h15 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨36, by decide⟩, true), (⟨4, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c218, some c21, some c20, some c109, some c210, some c213, some c140, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 57) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c218, c21, c20, c109, c210, c213, c140] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c218 := h 217 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c210 := h 209 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨43, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c272, some c269, some c49, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c272, c269, c49] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, false), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨42, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c782, some c76, some c763, some c370, some c371, some c579, some c70, some c152, some c97, some c465, some c464, some c12, some c798, some c799, some c187, some c316, some c313, some c60, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c782, c76, c763, c370, c371, c579, c70, c152, c97, c465, c464, c12, c798, c799, c187, c316, c313, c60] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c782 := derived782 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c371 := h 370 (by decide)
  have h5 : Entails.eval a c579 := derived579 a h
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c465 := derived465 a h
  have h10 : Entails.eval a c464 := derived464 a h
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c798 := derived798 a h
  have h13 : Entails.eval a c799 := derived799 a h
  have h14 : Entails.eval a c187 := h 186 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c313 := h 312 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c665, some c797, some c66, some c546, some c293, some c668, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c665, c797, c66, c546, c293, c668] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c665 := derived665 a h
  have h1 : Entails.eval a c797 := derived797 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c668 := derived668 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨41, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c745, some c665, some c797, some c66, some c384, some c382, some c782, some c800, some c99, some c98, some c14, some c70, some c91, some c772, some c371, some c315, some c158, some c184, some c165, some c328, some c801, some c258, some c271, some c45, some c50, some c291, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c546, c745, c665, c797, c66, c384, c382, c782, c800, c99, c98, c14, c70, c91, c772, c371, c315, c158, c184, c165, c328, c801, c258, c271, c45, c50, c291] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c797 := derived797 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c384 := h 383 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c782 := derived782 a h
  have h8 : Entails.eval a c800 := derived800 a h
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c91 := h 90 (by decide)
  have h14 : Entails.eval a c772 := derived772 a h
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  have h17 : Entails.eval a c158 := h 157 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c165 := h 164 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c801 := derived801 a h
  have h22 : Entails.eval a c258 := h 257 (by decide)
  have h23 : Entails.eval a c271 := h 270 (by decide)
  have h24 : Entails.eval a c45 := h 44 (by decide)
  have h25 : Entails.eval a c50 := h 49 (by decide)
  have h26 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c665, some c797, some c66, some c384, some c382, some c745, some c546, some c802, some c151, some c770, some c380, some c579, some c516, some c99, some c98, some c91, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c665, c797, c66, c384, c382, c745, c546, c802, c151, c770, c380, c579, c516, c99, c98, c91] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c665 := derived665 a h
  have h1 : Entails.eval a c797 := derived797 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c745 := derived745 a h
  have h6 : Entails.eval a c546 := derived546 a h
  have h7 : Entails.eval a c802 := derived802 a h
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c770 := derived770 a h
  have h10 : Entails.eval a c380 := h 379 (by decide)
  have h11 : Entails.eval a c579 := derived579 a h
  have h12 : Entails.eval a c516 := derived516 a h
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c98 := h 97 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, false), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c158, some c165, some c184, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c158, c165, c184] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c158 := h 157 (by decide)
  have h1 : Entails.eval a c165 := h 164 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨12, by decide⟩, false), (⟨39, by decide⟩, true), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨9, by decide⟩, false), (⟨46, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c50, some c277, some c306, some c263, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c117, c50, c277, c306, c263] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c108, some c242, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c115, c108, c242] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c803, some c546, some c745, some c665, some c797, some c66, some c384, some c382, some c782, some c99, some c98, some c70, some c91, some c772, some c380, some c770, some c147, some c356, some c14, some c433, some c375, some c321, some c804, some c771, some c376, some c81, some c15, some c699, some c163, some c183, some c805, some c806, some c22, some c187, some c195, some c133, some c126, some c38, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c803, c546, c745, c665, c797, c66, c384, c382, c782, c99, c98, c70, c91, c772, c380, c770, c147, c356, c14, c433, c375, c321, c804, c771, c376, c81, c15, c699, c163, c183, c805, c806, c22, c187, c195, c133, c126, c38] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c803 := derived803 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c797 := derived797 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c782 := derived782 a h
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c772 := derived772 a h
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c770 := derived770 a h
  have h16 : Entails.eval a c147 := h 146 (by decide)
  have h17 : Entails.eval a c356 := h 355 (by decide)
  have h18 : Entails.eval a c14 := h 13 (by decide)
  have h19 : Entails.eval a c433 := derived433 a h
  have h20 : Entails.eval a c375 := h 374 (by decide)
  have h21 : Entails.eval a c321 := h 320 (by decide)
  have h22 : Entails.eval a c804 := derived804 a h
  have h23 : Entails.eval a c771 := derived771 a h
  have h24 : Entails.eval a c376 := h 375 (by decide)
  have h25 : Entails.eval a c81 := h 80 (by decide)
  have h26 : Entails.eval a c15 := h 14 (by decide)
  have h27 : Entails.eval a c699 := derived699 a h
  have h28 : Entails.eval a c163 := h 162 (by decide)
  have h29 : Entails.eval a c183 := h 182 (by decide)
  have h30 : Entails.eval a c805 := derived805 a h
  have h31 : Entails.eval a c806 := derived806 a h
  have h32 : Entails.eval a c22 := h 21 (by decide)
  have h33 : Entails.eval a c187 := h 186 (by decide)
  have h34 : Entails.eval a c195 := h 194 (by decide)
  have h35 : Entails.eval a c133 := h 132 (by decide)
  have h36 : Entails.eval a c126 := h 125 (by decide)
  have h37 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c91, some c88, some c97, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c91, c88, c97] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨43, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c808, some c465, some c97, some c70, some c771, some c57, some c41, some c335, some c297, some c38, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c808, c465, c97, c70, c771, c57, c41, c335, c297, c38] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c808 := derived808 a h
  have h1 : Entails.eval a c465 := derived465 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c771 := derived771 a h
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c335 := h 334 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨43, by decide⟩, false), (⟨7, by decide⟩, true), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c770, some c781, some c516, some c380, some c375, some c363, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c151, c770, c781, c516, c380, c375, c363] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c770 := derived770 a h
  have h2 : Entails.eval a c781 := derived781 a h
  have h3 : Entails.eval a c516 := derived516 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨12, by decide⟩, true), (⟨43, by decide⟩, false), (⟨7, by decide⟩, true), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c150, some c780, some c516, some c375, some c365, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c150, c780, c516, c375, c365] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c150 := h 149 (by decide)
  have h1 : Entails.eval a c780 := derived780 a h
  have h2 : Entails.eval a c516 := derived516 a h
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c152, some c4, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c70, c152, c4] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c665, some c745, some c797, some c66, some c382, some c384, some c782, some c803, some c807, some c76, some c763, some c809, some c810, some c12, some c811, some c380, some c147, some c356, some c516, some c812, some c419, some c163, some c15, some c764, some c765, some c297, some c283, some c341, some c327, some c264, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c546, c665, c745, c797, c66, c382, c384, c782, c803, c807, c76, c763, c809, c810, c12, c811, c380, c147, c356, c516, c812, c419, c163, c15, c764, c765, c297, c283, c341, c327, c264] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c797 := derived797 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c782 := derived782 a h
  have h8 : Entails.eval a c803 := derived803 a h
  have h9 : Entails.eval a c807 := derived807 a h
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c763 := derived763 a h
  have h12 : Entails.eval a c809 := derived809 a h
  have h13 : Entails.eval a c810 := derived810 a h
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c811 := derived811 a h
  have h16 : Entails.eval a c380 := h 379 (by decide)
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c516 := derived516 a h
  have h20 : Entails.eval a c812 := derived812 a h
  have h21 : Entails.eval a c419 := derived419 a h
  have h22 : Entails.eval a c163 := h 162 (by decide)
  have h23 : Entails.eval a c15 := h 14 (by decide)
  have h24 : Entails.eval a c764 := derived764 a h
  have h25 : Entails.eval a c765 := derived765 a h
  have h26 : Entails.eval a c297 := h 296 (by decide)
  have h27 : Entails.eval a c283 := h 282 (by decide)
  have h28 : Entails.eval a c341 := h 340 (by decide)
  have h29 : Entails.eval a c327 := h 326 (by decide)
  have h30 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨45, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨48, by decide⟩, true), (⟨46, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c813, some c96, some c98, some c71, some c90, some c516, some c97, some c163, some c15, some c764, some c765, some c761, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 57) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c382, c813, c96, c98, c71, c90, c516, c97, c163, c15, c764, c765, c761] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c382 := h 381 (by decide)
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c516 := derived516 a h
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c764 := derived764 a h
  have h11 : Entails.eval a c765 := derived765 a h
  have h12 : Entails.eval a c761 := derived761 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c81, some c15, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 57) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c163, c81, c15] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c153, some c5, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 57) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c71, c153, c5] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c153 := h 152 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, true), (⟨46, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c376, some c815, some c96, some c98, some c814, some c87, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 57) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c813, c376, c815, c96, c98, c814, c87] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c815 := derived815 a h
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c814 := derived814 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c98, some c87, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 57) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c96, c98, c87] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived818

end CochromaticTwenty.Certificates.B16_8_0Enumerating
