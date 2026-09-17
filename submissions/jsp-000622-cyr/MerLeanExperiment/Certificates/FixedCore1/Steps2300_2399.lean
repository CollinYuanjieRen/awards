import MerLeanExperiment.Certificates.FixedCore1.Steps2200_2299

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8181 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8181 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8173, some c8171, some c8159, some c7849, some c7941, some c8175, some c8011, some c8176, some c8177, some c8180, some c7998, some c8178, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8181 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8181 : lratChecker f8181 p8181 = .success := by decide +kernel
theorem unsat8181 : Unsatisfiable (PosFin 65) f8181 := by
  apply lratCheckerSound f8181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8181
  · intro a ha; simp [p8181] at ha; subst a; trivial
  · exact checked8181
theorem derived8181 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8181 := by
  apply localUnsat_implies_entails f8181 [c8173, c8171, c8159, c7849, c7941, c8175, c8011, c8176, c8177, c8180, c7998, c8178] c8181 unsat8181 (by rfl) a
  have h0 : Entails.eval a c8173 := derived8173 a h
  have h1 : Entails.eval a c8171 := derived8171 a h
  have h2 : Entails.eval a c8159 := derived8159 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c7941 := derived7941 a h
  have h5 : Entails.eval a c8175 := derived8175 a h
  have h6 : Entails.eval a c8011 := derived8011 a h
  have h7 : Entails.eval a c8176 := derived8176 a h
  have h8 : Entails.eval a c8177 := derived8177 a h
  have h9 : Entails.eval a c8180 := derived8180 a h
  have h10 : Entails.eval a c7998 := derived7998 a h
  have h11 : Entails.eval a c8178 := derived8178 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8182 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8182 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8177, some c8163, some c509, some c640, some c448, some c2002, some c2140, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8182 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8182 : lratChecker f8182 p8182 = .success := by decide +kernel
theorem unsat8182 : Unsatisfiable (PosFin 65) f8182 := by
  apply lratCheckerSound f8182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8182
  · intro a ha; simp [p8182] at ha; subst a; trivial
  · exact checked8182
theorem derived8182 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8182 := by
  apply localUnsat_implies_entails f8182 [c7849, c8177, c8163, c509, c640, c448, c2002, c2140] c8182 unsat8182 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8177 := derived8177 a h
  have h2 : Entails.eval a c8163 := derived8163 a h
  have h3 : Entails.eval a c509 := h 508 (by decide)
  have h4 : Entails.eval a c640 := h 639 (by decide)
  have h5 : Entails.eval a c448 := h 447 (by decide)
  have h6 : Entails.eval a c2002 := h 2001 (by decide)
  have h7 : Entails.eval a c2140 := h 2139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8183 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8183 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1259, some c8178, some c1574, some c1986, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8183 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8183 : lratChecker f8183 p8183 = .success := by decide +kernel
theorem unsat8183 : Unsatisfiable (PosFin 65) f8183 := by
  apply lratCheckerSound f8183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8183
  · intro a ha; simp [p8183] at ha; subst a; trivial
  · exact checked8183
theorem derived8183 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8183 := by
  apply localUnsat_implies_entails f8183 [c1259, c8178, c1574, c1986] c8183 unsat8183 (by rfl) a
  have h0 : Entails.eval a c1259 := h 1258 (by decide)
  have h1 : Entails.eval a c8178 := derived8178 a h
  have h2 : Entails.eval a c1574 := h 1573 (by decide)
  have h3 : Entails.eval a c1986 := h 1985 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8184 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8184 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c644, some c641, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8184 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8184 : lratChecker f8184 p8184 = .success := by decide +kernel
theorem unsat8184 : Unsatisfiable (PosFin 65) f8184 := by
  apply lratCheckerSound f8184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8184
  · intro a ha; simp [p8184] at ha; subst a; trivial
  · exact checked8184
theorem derived8184 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8184 := by
  apply localUnsat_implies_entails f8184 [c644, c641] c8184 unsat8184 (by rfl) a
  have h0 : Entails.eval a c644 := h 643 (by decide)
  have h1 : Entails.eval a c641 := h 640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8185 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8185 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c443, some c1996, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8185 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8185 : lratChecker f8185 p8185 = .success := by decide +kernel
theorem unsat8185 : Unsatisfiable (PosFin 65) f8185 := by
  apply lratCheckerSound f8185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8185
  · intro a ha; simp [p8185] at ha; subst a; trivial
  · exact checked8185
theorem derived8185 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8185 := by
  apply localUnsat_implies_entails f8185 [c443, c1996] c8185 unsat8185 (by rfl) a
  have h0 : Entails.eval a c443 := h 442 (by decide)
  have h1 : Entails.eval a c1996 := h 1995 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8186 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8186 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c430, some c441, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8186 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8186 : lratChecker f8186 p8186 = .success := by decide +kernel
theorem unsat8186 : Unsatisfiable (PosFin 65) f8186 := by
  apply lratCheckerSound f8186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8186
  · intro a ha; simp [p8186] at ha; subst a; trivial
  · exact checked8186
theorem derived8186 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8186 := by
  apply localUnsat_implies_entails f8186 [c430, c441] c8186 unsat8186 (by rfl) a
  have h0 : Entails.eval a c430 := h 429 (by decide)
  have h1 : Entails.eval a c441 := h 440 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8187 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8187 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8181, some c8173, some c8171, some c8159, some c7849, some c8182, some c8183, some c8184, some c8185, some c8186, some c2015, some c1999, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8187 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8187 : lratChecker f8187 p8187 = .success := by decide +kernel
theorem unsat8187 : Unsatisfiable (PosFin 65) f8187 := by
  apply lratCheckerSound f8187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8187
  · intro a ha; simp [p8187] at ha; subst a; trivial
  · exact checked8187
theorem derived8187 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8187 := by
  apply localUnsat_implies_entails f8187 [c8181, c8173, c8171, c8159, c7849, c8182, c8183, c8184, c8185, c8186, c2015, c1999] c8187 unsat8187 (by rfl) a
  have h0 : Entails.eval a c8181 := derived8181 a h
  have h1 : Entails.eval a c8173 := derived8173 a h
  have h2 : Entails.eval a c8171 := derived8171 a h
  have h3 : Entails.eval a c8159 := derived8159 a h
  have h4 : Entails.eval a c7849 := derived7849 a h
  have h5 : Entails.eval a c8182 := derived8182 a h
  have h6 : Entails.eval a c8183 := derived8183 a h
  have h7 : Entails.eval a c8184 := derived8184 a h
  have h8 : Entails.eval a c8185 := derived8185 a h
  have h9 : Entails.eval a c8186 := derived8186 a h
  have h10 : Entails.eval a c2015 := h 2014 (by decide)
  have h11 : Entails.eval a c1999 := h 1998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8188 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8188 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7766, some c1330, some c7343, some c2147, some c1574, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8188 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8188 : lratChecker f8188 p8188 = .success := by decide +kernel
theorem unsat8188 : Unsatisfiable (PosFin 65) f8188 := by
  apply lratCheckerSound f8188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8188
  · intro a ha; simp [p8188] at ha; subst a; trivial
  · exact checked8188
theorem derived8188 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8188 := by
  apply localUnsat_implies_entails f8188 [c7766, c1330, c7343, c2147, c1574] c8188 unsat8188 (by rfl) a
  have h0 : Entails.eval a c7766 := derived7766 a h
  have h1 : Entails.eval a c1330 := h 1329 (by decide)
  have h2 : Entails.eval a c7343 := derived7343 a h
  have h3 : Entails.eval a c2147 := h 2146 (by decide)
  have h4 : Entails.eval a c1574 := h 1573 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8189 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8189 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8177, some c448, some c1983, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8189 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8189 : lratChecker f8189 p8189 = .success := by decide +kernel
theorem unsat8189 : Unsatisfiable (PosFin 65) f8189 := by
  apply lratCheckerSound f8189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8189
  · intro a ha; simp [p8189] at ha; subst a; trivial
  · exact checked8189
theorem derived8189 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8189 := by
  apply localUnsat_implies_entails f8189 [c8177, c448, c1983] c8189 unsat8189 (by rfl) a
  have h0 : Entails.eval a c8177 := derived8177 a h
  have h1 : Entails.eval a c448 := h 447 (by decide)
  have h2 : Entails.eval a c1983 := h 1982 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8190 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8190 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c7849, some c8171, some c8173, some c8181, some c8187, some c8188, some c8184, some c8189, some c8185, some c8186, some c2015, some c1999, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8190 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8190 : lratChecker f8190 p8190 = .success := by decide +kernel
theorem unsat8190 : Unsatisfiable (PosFin 65) f8190 := by
  apply lratCheckerSound f8190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8190
  · intro a ha; simp [p8190] at ha; subst a; trivial
  · exact checked8190
theorem derived8190 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8190 := by
  apply localUnsat_implies_entails f8190 [c8159, c7849, c8171, c8173, c8181, c8187, c8188, c8184, c8189, c8185, c8186, c2015, c1999] c8190 unsat8190 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8171 := derived8171 a h
  have h3 : Entails.eval a c8173 := derived8173 a h
  have h4 : Entails.eval a c8181 := derived8181 a h
  have h5 : Entails.eval a c8187 := derived8187 a h
  have h6 : Entails.eval a c8188 := derived8188 a h
  have h7 : Entails.eval a c8184 := derived8184 a h
  have h8 : Entails.eval a c8189 := derived8189 a h
  have h9 : Entails.eval a c8185 := derived8185 a h
  have h10 : Entails.eval a c8186 := derived8186 a h
  have h11 : Entails.eval a c2015 := h 2014 (by decide)
  have h12 : Entails.eval a c1999 := h 1998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8191 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8191 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c847, some c863, some c2677, some c846, some c854, some c2231, some c2359, some c2524, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8191 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8191 : lratChecker f8191 p8191 = .success := by decide +kernel
theorem unsat8191 : Unsatisfiable (PosFin 65) f8191 := by
  apply lratCheckerSound f8191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8191
  · intro a ha; simp [p8191] at ha; subst a; trivial
  · exact checked8191
theorem derived8191 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8191 := by
  apply localUnsat_implies_entails f8191 [c847, c863, c2677, c846, c854, c2231, c2359, c2524] c8191 unsat8191 (by rfl) a
  have h0 : Entails.eval a c847 := h 846 (by decide)
  have h1 : Entails.eval a c863 := h 862 (by decide)
  have h2 : Entails.eval a c2677 := h 2676 (by decide)
  have h3 : Entails.eval a c846 := h 845 (by decide)
  have h4 : Entails.eval a c854 := h 853 (by decide)
  have h5 : Entails.eval a c2231 := h 2230 (by decide)
  have h6 : Entails.eval a c2359 := h 2358 (by decide)
  have h7 : Entails.eval a c2524 := h 2523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8192 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8192 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8191, some c864, some c855, some c848, some c845, some c837, some c846, some c425, some c617, some c1899, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8192 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8192 : lratChecker f8192 p8192 = .success := by decide +kernel
theorem unsat8192 : Unsatisfiable (PosFin 65) f8192 := by
  apply lratCheckerSound f8192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8192
  · intro a ha; simp [p8192] at ha; subst a; trivial
  · exact checked8192
theorem derived8192 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8192 := by
  apply localUnsat_implies_entails f8192 [c8191, c864, c855, c848, c845, c837, c846, c425, c617, c1899] c8192 unsat8192 (by rfl) a
  have h0 : Entails.eval a c8191 := derived8191 a h
  have h1 : Entails.eval a c864 := h 863 (by decide)
  have h2 : Entails.eval a c855 := h 854 (by decide)
  have h3 : Entails.eval a c848 := h 847 (by decide)
  have h4 : Entails.eval a c845 := h 844 (by decide)
  have h5 : Entails.eval a c837 := h 836 (by decide)
  have h6 : Entails.eval a c846 := h 845 (by decide)
  have h7 : Entails.eval a c425 := h 424 (by decide)
  have h8 : Entails.eval a c617 := h 616 (by decide)
  have h9 : Entails.eval a c1899 := h 1898 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8193 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8193 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8190, some c8159, some c7849, some c7941, some c8192, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8193 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8193 : lratChecker f8193 p8193 = .success := by decide +kernel
theorem unsat8193 : Unsatisfiable (PosFin 65) f8193 := by
  apply lratCheckerSound f8193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8193
  · intro a ha; simp [p8193] at ha; subst a; trivial
  · exact checked8193
theorem derived8193 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8193 := by
  apply localUnsat_implies_entails f8193 [c8190, c8159, c7849, c7941, c8192] c8193 unsat8193 (by rfl) a
  have h0 : Entails.eval a c8190 := derived8190 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c7941 := derived7941 a h
  have h4 : Entails.eval a c8192 := derived8192 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8194 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8194 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c847, some c863, some c1216, some c2672, some c2357, some c1168, some c2638, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8194 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8194 : lratChecker f8194 p8194 = .success := by decide +kernel
theorem unsat8194 : Unsatisfiable (PosFin 65) f8194 := by
  apply lratCheckerSound f8194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8194
  · intro a ha; simp [p8194] at ha; subst a; trivial
  · exact checked8194
theorem derived8194 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8194 := by
  apply localUnsat_implies_entails f8194 [c847, c863, c1216, c2672, c2357, c1168, c2638] c8194 unsat8194 (by rfl) a
  have h0 : Entails.eval a c847 := h 846 (by decide)
  have h1 : Entails.eval a c863 := h 862 (by decide)
  have h2 : Entails.eval a c1216 := h 1215 (by decide)
  have h3 : Entails.eval a c2672 := h 2671 (by decide)
  have h4 : Entails.eval a c2357 := h 2356 (by decide)
  have h5 : Entails.eval a c1168 := h 1167 (by decide)
  have h6 : Entails.eval a c2638 := h 2637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8195 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8195 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1216, some c2672, some c2358, some c1168, some c2638, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8195 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8195 : lratChecker f8195 p8195 = .success := by decide +kernel
theorem unsat8195 : Unsatisfiable (PosFin 65) f8195 := by
  apply lratCheckerSound f8195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8195
  · intro a ha; simp [p8195] at ha; subst a; trivial
  · exact checked8195
theorem derived8195 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8195 := by
  apply localUnsat_implies_entails f8195 [c1216, c2672, c2358, c1168, c2638] c8195 unsat8195 (by rfl) a
  have h0 : Entails.eval a c1216 := h 1215 (by decide)
  have h1 : Entails.eval a c2672 := h 2671 (by decide)
  have h2 : Entails.eval a c2358 := h 2357 (by decide)
  have h3 : Entails.eval a c1168 := h 1167 (by decide)
  have h4 : Entails.eval a c2638 := h 2637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8196 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8196 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8194, some c8195, some c844, some c845, some c855, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8196 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8196 : lratChecker f8196 p8196 = .success := by decide +kernel
theorem unsat8196 : Unsatisfiable (PosFin 65) f8196 := by
  apply lratCheckerSound f8196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8196
  · intro a ha; simp [p8196] at ha; subst a; trivial
  · exact checked8196
theorem derived8196 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8196 := by
  apply localUnsat_implies_entails f8196 [c8194, c8195, c844, c845, c855] c8196 unsat8196 (by rfl) a
  have h0 : Entails.eval a c8194 := derived8194 a h
  have h1 : Entails.eval a c8195 := derived8195 a h
  have h2 : Entails.eval a c844 := h 843 (by decide)
  have h3 : Entails.eval a c845 := h 844 (by decide)
  have h4 : Entails.eval a c855 := h 854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8197 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8197 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8190, some c8159, some c7849, some c8193, some c8196, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8197 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8197 : lratChecker f8197 p8197 = .success := by decide +kernel
theorem unsat8197 : Unsatisfiable (PosFin 65) f8197 := by
  apply lratCheckerSound f8197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8197
  · intro a ha; simp [p8197] at ha; subst a; trivial
  · exact checked8197
theorem derived8197 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8197 := by
  apply localUnsat_implies_entails f8197 [c8190, c8159, c7849, c8193, c8196] c8197 unsat8197 (by rfl) a
  have h0 : Entails.eval a c8190 := derived8190 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8193 := derived8193 a h
  have h4 : Entails.eval a c8196 := derived8196 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8198 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8198 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1542, some c1260, some c1784, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8198 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8198 : lratChecker f8198 p8198 = .success := by decide +kernel
theorem unsat8198 : Unsatisfiable (PosFin 65) f8198 := by
  apply lratCheckerSound f8198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8198
  · intro a ha; simp [p8198] at ha; subst a; trivial
  · exact checked8198
theorem derived8198 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8198 := by
  apply localUnsat_implies_entails f8198 [c1542, c1260, c1784] c8198 unsat8198 (by rfl) a
  have h0 : Entails.eval a c1542 := h 1541 (by decide)
  have h1 : Entails.eval a c1260 := h 1259 (by decide)
  have h2 : Entails.eval a c1784 := h 1783 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8199 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8199 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8198, some c7946, some c2231, some c2359, some c1060, some c1558, some c1173, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8199 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8199 : lratChecker f8199 p8199 = .success := by decide +kernel
theorem unsat8199 : Unsatisfiable (PosFin 65) f8199 := by
  apply lratCheckerSound f8199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8199
  · intro a ha; simp [p8199] at ha; subst a; trivial
  · exact checked8199
theorem derived8199 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8199 := by
  apply localUnsat_implies_entails f8199 [c8198, c7946, c2231, c2359, c1060, c1558, c1173] c8199 unsat8199 (by rfl) a
  have h0 : Entails.eval a c8198 := derived8198 a h
  have h1 : Entails.eval a c7946 := derived7946 a h
  have h2 : Entails.eval a c2231 := h 2230 (by decide)
  have h3 : Entails.eval a c2359 := h 2358 (by decide)
  have h4 : Entails.eval a c1060 := h 1059 (by decide)
  have h5 : Entails.eval a c1558 := h 1557 (by decide)
  have h6 : Entails.eval a c1173 := h 1172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8200 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8200 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1299, some c1558, some c1455, some c2072, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p8200 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8200 : lratChecker f8200 p8200 = .success := by decide +kernel
theorem unsat8200 : Unsatisfiable (PosFin 65) f8200 := by
  apply lratCheckerSound f8200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8200
  · intro a ha; simp [p8200] at ha; subst a; trivial
  · exact checked8200
theorem derived8200 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8200 := by
  apply localUnsat_implies_entails f8200 [c1299, c1558, c1455, c2072] c8200 unsat8200 (by rfl) a
  have h0 : Entails.eval a c1299 := h 1298 (by decide)
  have h1 : Entails.eval a c1558 := h 1557 (by decide)
  have h2 : Entails.eval a c1455 := h 1454 (by decide)
  have h3 : Entails.eval a c2072 := h 2071 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8201 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8201 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8199, some c8175, some c7946, some c2359, some c8200, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8201 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8201 : lratChecker f8201 p8201 = .success := by decide +kernel
theorem unsat8201 : Unsatisfiable (PosFin 65) f8201 := by
  apply lratCheckerSound f8201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8201
  · intro a ha; simp [p8201] at ha; subst a; trivial
  · exact checked8201
theorem derived8201 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8201 := by
  apply localUnsat_implies_entails f8201 [c8199, c8175, c7946, c2359, c8200] c8201 unsat8201 (by rfl) a
  have h0 : Entails.eval a c8199 := derived8199 a h
  have h1 : Entails.eval a c8175 := derived8175 a h
  have h2 : Entails.eval a c7946 := derived7946 a h
  have h3 : Entails.eval a c2359 := h 2358 (by decide)
  have h4 : Entails.eval a c8200 := derived8200 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8202 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8202 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8197, some c8190, some c8159, some c7849, some c7941, some c8201, some c8177, some c8168, some c8186, some c8175, some c8030, some c1897, some c7998, some c8178, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8202 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8202 : lratChecker f8202 p8202 = .success := by decide +kernel
theorem unsat8202 : Unsatisfiable (PosFin 65) f8202 := by
  apply lratCheckerSound f8202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8202
  · intro a ha; simp [p8202] at ha; subst a; trivial
  · exact checked8202
theorem derived8202 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8202 := by
  apply localUnsat_implies_entails f8202 [c8197, c8190, c8159, c7849, c7941, c8201, c8177, c8168, c8186, c8175, c8030, c1897, c7998, c8178] c8202 unsat8202 (by rfl) a
  have h0 : Entails.eval a c8197 := derived8197 a h
  have h1 : Entails.eval a c8190 := derived8190 a h
  have h2 : Entails.eval a c8159 := derived8159 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c7941 := derived7941 a h
  have h5 : Entails.eval a c8201 := derived8201 a h
  have h6 : Entails.eval a c8177 := derived8177 a h
  have h7 : Entails.eval a c8168 := derived8168 a h
  have h8 : Entails.eval a c8186 := derived8186 a h
  have h9 : Entails.eval a c8175 := derived8175 a h
  have h10 : Entails.eval a c8030 := derived8030 a h
  have h11 : Entails.eval a c1897 := h 1896 (by decide)
  have h12 : Entails.eval a c7998 := derived7998 a h
  have h13 : Entails.eval a c8178 := derived8178 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8203 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8203 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2215, some c1983, some c2080, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8203 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8203 : lratChecker f8203 p8203 = .success := by decide +kernel
theorem unsat8203 : Unsatisfiable (PosFin 65) f8203 := by
  apply lratCheckerSound f8203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8203
  · intro a ha; simp [p8203] at ha; subst a; trivial
  · exact checked8203
theorem derived8203 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8203 := by
  apply localUnsat_implies_entails f8203 [c2215, c1983, c2080] c8203 unsat8203 (by rfl) a
  have h0 : Entails.eval a c2215 := h 2214 (by decide)
  have h1 : Entails.eval a c1983 := h 1982 (by decide)
  have h2 : Entails.eval a c2080 := h 2079 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8204 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8204 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8177, some c8203, some c617, some c2467, some c640, some c2228, some c2358, some c2522, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8204 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8204 : lratChecker f8204 p8204 = .success := by decide +kernel
theorem unsat8204 : Unsatisfiable (PosFin 65) f8204 := by
  apply lratCheckerSound f8204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8204
  · intro a ha; simp [p8204] at ha; subst a; trivial
  · exact checked8204
theorem derived8204 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8204 := by
  apply localUnsat_implies_entails f8204 [c8177, c8203, c617, c2467, c640, c2228, c2358, c2522] c8204 unsat8204 (by rfl) a
  have h0 : Entails.eval a c8177 := derived8177 a h
  have h1 : Entails.eval a c8203 := derived8203 a h
  have h2 : Entails.eval a c617 := h 616 (by decide)
  have h3 : Entails.eval a c2467 := h 2466 (by decide)
  have h4 : Entails.eval a c640 := h 639 (by decide)
  have h5 : Entails.eval a c2228 := h 2227 (by decide)
  have h6 : Entails.eval a c2358 := h 2357 (by decide)
  have h7 : Entails.eval a c2522 := h 2521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8205 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8205 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8168, some c8184, some c8185, some c8186, some c1909, some c2015, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8205 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8205 : lratChecker f8205 p8205 = .success := by decide +kernel
theorem unsat8205 : Unsatisfiable (PosFin 65) f8205 := by
  apply lratCheckerSound f8205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8205
  · intro a ha; simp [p8205] at ha; subst a; trivial
  · exact checked8205
theorem derived8205 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8205 := by
  apply localUnsat_implies_entails f8205 [c8168, c8184, c8185, c8186, c1909, c2015] c8205 unsat8205 (by rfl) a
  have h0 : Entails.eval a c8168 := derived8168 a h
  have h1 : Entails.eval a c8184 := derived8184 a h
  have h2 : Entails.eval a c8185 := derived8185 a h
  have h3 : Entails.eval a c8186 := derived8186 a h
  have h4 : Entails.eval a c1909 := h 1908 (by decide)
  have h5 : Entails.eval a c2015 := h 2014 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8206 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8206 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c7849, some c8190, some c8197, some c8202, some c8204, some c8168, some c8205, some c8178, some c8183, some c1895, some c2216, some c1300, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8206 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8206 : lratChecker f8206 p8206 = .success := by decide +kernel
theorem unsat8206 : Unsatisfiable (PosFin 65) f8206 := by
  apply lratCheckerSound f8206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8206
  · intro a ha; simp [p8206] at ha; subst a; trivial
  · exact checked8206
theorem derived8206 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8206 := by
  apply localUnsat_implies_entails f8206 [c8159, c7849, c8190, c8197, c8202, c8204, c8168, c8205, c8178, c8183, c1895, c2216, c1300] c8206 unsat8206 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8190 := derived8190 a h
  have h3 : Entails.eval a c8197 := derived8197 a h
  have h4 : Entails.eval a c8202 := derived8202 a h
  have h5 : Entails.eval a c8204 := derived8204 a h
  have h6 : Entails.eval a c8168 := derived8168 a h
  have h7 : Entails.eval a c8205 := derived8205 a h
  have h8 : Entails.eval a c8178 := derived8178 a h
  have h9 : Entails.eval a c8183 := derived8183 a h
  have h10 : Entails.eval a c1895 := h 1894 (by decide)
  have h11 : Entails.eval a c2216 := h 2215 (by decide)
  have h12 : Entails.eval a c1300 := h 1299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8207 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8207 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8124, some c8161, some c906, some c8104, some c8176, some c642, some c2470, some c631, some c8077, some c1326, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8207 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8207 : lratChecker f8207 p8207 = .success := by decide +kernel
theorem unsat8207 : Unsatisfiable (PosFin 65) f8207 := by
  apply lratCheckerSound f8207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8207
  · intro a ha; simp [p8207] at ha; subst a; trivial
  · exact checked8207
theorem derived8207 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8207 := by
  apply localUnsat_implies_entails f8207 [c8124, c8161, c906, c8104, c8176, c642, c2470, c631, c8077, c1326] c8207 unsat8207 (by rfl) a
  have h0 : Entails.eval a c8124 := derived8124 a h
  have h1 : Entails.eval a c8161 := derived8161 a h
  have h2 : Entails.eval a c906 := h 905 (by decide)
  have h3 : Entails.eval a c8104 := derived8104 a h
  have h4 : Entails.eval a c8176 := derived8176 a h
  have h5 : Entails.eval a c642 := h 641 (by decide)
  have h6 : Entails.eval a c2470 := h 2469 (by decide)
  have h7 : Entails.eval a c631 := h 630 (by decide)
  have h8 : Entails.eval a c8077 := derived8077 a h
  have h9 : Entails.eval a c1326 := h 1325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8208 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8208 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c901, some c8176, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p8208 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8208 : lratChecker f8208 p8208 = .success := by decide +kernel
theorem unsat8208 : Unsatisfiable (PosFin 65) f8208 := by
  apply lratCheckerSound f8208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8208
  · intro a ha; simp [p8208] at ha; subst a; trivial
  · exact checked8208
theorem derived8208 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8208 := by
  apply localUnsat_implies_entails f8208 [c901, c8176] c8208 unsat8208 (by rfl) a
  have h0 : Entails.eval a c901 := h 900 (by decide)
  have h1 : Entails.eval a c8176 := derived8176 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8209 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8209 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8208, some c8207, some c642, some c8164, some c637, some c631, some c7597, some c627, some c614, some c7974, some c923, some c921, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8209 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8209 : lratChecker f8209 p8209 = .success := by decide +kernel
theorem unsat8209 : Unsatisfiable (PosFin 65) f8209 := by
  apply lratCheckerSound f8209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8209
  · intro a ha; simp [p8209] at ha; subst a; trivial
  · exact checked8209
theorem derived8209 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8209 := by
  apply localUnsat_implies_entails f8209 [c8208, c8207, c642, c8164, c637, c631, c7597, c627, c614, c7974, c923, c921] c8209 unsat8209 (by rfl) a
  have h0 : Entails.eval a c8208 := derived8208 a h
  have h1 : Entails.eval a c8207 := derived8207 a h
  have h2 : Entails.eval a c642 := h 641 (by decide)
  have h3 : Entails.eval a c8164 := derived8164 a h
  have h4 : Entails.eval a c637 := h 636 (by decide)
  have h5 : Entails.eval a c631 := h 630 (by decide)
  have h6 : Entails.eval a c7597 := derived7597 a h
  have h7 : Entails.eval a c627 := h 626 (by decide)
  have h8 : Entails.eval a c614 := h 613 (by decide)
  have h9 : Entails.eval a c7974 := derived7974 a h
  have h10 : Entails.eval a c923 := h 922 (by decide)
  have h11 : Entails.eval a c921 := h 920 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8210 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8210 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c441, some c447, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8210 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8210 : lratChecker f8210 p8210 = .success := by decide +kernel
theorem unsat8210 : Unsatisfiable (PosFin 65) f8210 := by
  apply lratCheckerSound f8210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8210
  · intro a ha; simp [p8210] at ha; subst a; trivial
  · exact checked8210
theorem derived8210 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8210 := by
  apply localUnsat_implies_entails f8210 [c441, c447] c8210 unsat8210 (by rfl) a
  have h0 : Entails.eval a c441 := h 440 (by decide)
  have h1 : Entails.eval a c447 := h 446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8211 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8211 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8124, some c8207, some c8175, some c8209, some c8210, some c2013, some c2009, some c2006, some c1978, some c1309, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8211 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8211 : lratChecker f8211 p8211 = .success := by decide +kernel
theorem unsat8211 : Unsatisfiable (PosFin 65) f8211 := by
  apply lratCheckerSound f8211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8211
  · intro a ha; simp [p8211] at ha; subst a; trivial
  · exact checked8211
theorem derived8211 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8211 := by
  apply localUnsat_implies_entails f8211 [c8124, c8207, c8175, c8209, c8210, c2013, c2009, c2006, c1978, c1309] c8211 unsat8211 (by rfl) a
  have h0 : Entails.eval a c8124 := derived8124 a h
  have h1 : Entails.eval a c8207 := derived8207 a h
  have h2 : Entails.eval a c8175 := derived8175 a h
  have h3 : Entails.eval a c8209 := derived8209 a h
  have h4 : Entails.eval a c8210 := derived8210 a h
  have h5 : Entails.eval a c2013 := h 2012 (by decide)
  have h6 : Entails.eval a c2009 := h 2008 (by decide)
  have h7 : Entails.eval a c2006 := h 2005 (by decide)
  have h8 : Entails.eval a c1978 := h 1977 (by decide)
  have h9 : Entails.eval a c1309 := h 1308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8212 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨31, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8212 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1542, some c1260, some c1786, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8212 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8212 : lratChecker f8212 p8212 = .success := by decide +kernel
theorem unsat8212 : Unsatisfiable (PosFin 65) f8212 := by
  apply lratCheckerSound f8212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8212
  · intro a ha; simp [p8212] at ha; subst a; trivial
  · exact checked8212
theorem derived8212 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8212 := by
  apply localUnsat_implies_entails f8212 [c1542, c1260, c1786] c8212 unsat8212 (by rfl) a
  have h0 : Entails.eval a c1542 := h 1541 (by decide)
  have h1 : Entails.eval a c1260 := h 1259 (by decide)
  have h2 : Entails.eval a c1786 := h 1785 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8213 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨31, by decide⟩, true), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8213 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8124, some c8168, some c642, some c2470, some c637, some c631, some c2231, some c627, some c565, some c582, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8213 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8213 : lratChecker f8213 p8213 = .success := by decide +kernel
theorem unsat8213 : Unsatisfiable (PosFin 65) f8213 := by
  apply lratCheckerSound f8213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8213
  · intro a ha; simp [p8213] at ha; subst a; trivial
  · exact checked8213
theorem derived8213 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8213 := by
  apply localUnsat_implies_entails f8213 [c8124, c8168, c642, c2470, c637, c631, c2231, c627, c565, c582] c8213 unsat8213 (by rfl) a
  have h0 : Entails.eval a c8124 := derived8124 a h
  have h1 : Entails.eval a c8168 := derived8168 a h
  have h2 : Entails.eval a c642 := h 641 (by decide)
  have h3 : Entails.eval a c2470 := h 2469 (by decide)
  have h4 : Entails.eval a c637 := h 636 (by decide)
  have h5 : Entails.eval a c631 := h 630 (by decide)
  have h6 : Entails.eval a c2231 := h 2230 (by decide)
  have h7 : Entails.eval a c627 := h 626 (by decide)
  have h8 : Entails.eval a c565 := h 564 (by decide)
  have h9 : Entails.eval a c582 := h 581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8214 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8214 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c452, some c440, some c447, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8214 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8214 : lratChecker f8214 p8214 = .success := by decide +kernel
theorem unsat8214 : Unsatisfiable (PosFin 65) f8214 := by
  apply lratCheckerSound f8214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8214
  · intro a ha; simp [p8214] at ha; subst a; trivial
  · exact checked8214
theorem derived8214 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8214 := by
  apply localUnsat_implies_entails f8214 [c452, c440, c447] c8214 unsat8214 (by rfl) a
  have h0 : Entails.eval a c452 := h 451 (by decide)
  have h1 : Entails.eval a c440 := h 439 (by decide)
  have h2 : Entails.eval a c447 := h 446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8215 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8215 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8214, some c8213, some c1896, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8215 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8215 : lratChecker f8215 p8215 = .success := by decide +kernel
theorem unsat8215 : Unsatisfiable (PosFin 65) f8215 := by
  apply lratCheckerSound f8215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8215
  · intro a ha; simp [p8215] at ha; subst a; trivial
  · exact checked8215
theorem derived8215 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8215 := by
  apply localUnsat_implies_entails f8215 [c8214, c8213, c1896] c8215 unsat8215 (by rfl) a
  have h0 : Entails.eval a c8214 := derived8214 a h
  have h1 : Entails.eval a c8213 := derived8213 a h
  have h2 : Entails.eval a c1896 := h 1895 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8216 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8216 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8206, some c8124, some c8159, some c7941, some c8211, some c8201, some c8214, some c8215, some c8175, some c8030, some c1936, some c1897, some c1347, some c2361, some c2525, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8216 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8216 : lratChecker f8216 p8216 = .success := by decide +kernel
theorem unsat8216 : Unsatisfiable (PosFin 65) f8216 := by
  apply lratCheckerSound f8216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8216
  · intro a ha; simp [p8216] at ha; subst a; trivial
  · exact checked8216
theorem derived8216 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8216 := by
  apply localUnsat_implies_entails f8216 [c7849, c8206, c8124, c8159, c7941, c8211, c8201, c8214, c8215, c8175, c8030, c1936, c1897, c1347, c2361, c2525] c8216 unsat8216 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8206 := derived8206 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c8159 := derived8159 a h
  have h4 : Entails.eval a c7941 := derived7941 a h
  have h5 : Entails.eval a c8211 := derived8211 a h
  have h6 : Entails.eval a c8201 := derived8201 a h
  have h7 : Entails.eval a c8214 := derived8214 a h
  have h8 : Entails.eval a c8215 := derived8215 a h
  have h9 : Entails.eval a c8175 := derived8175 a h
  have h10 : Entails.eval a c8030 := derived8030 a h
  have h11 : Entails.eval a c1936 := h 1935 (by decide)
  have h12 : Entails.eval a c1897 := h 1896 (by decide)
  have h13 : Entails.eval a c1347 := h 1346 (by decide)
  have h14 : Entails.eval a c2361 := h 2360 (by decide)
  have h15 : Entails.eval a c2525 := h 2524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8217 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8217 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8124, some c445, some c638, some c2008, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8217 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8217 : lratChecker f8217 p8217 = .success := by decide +kernel
theorem unsat8217 : Unsatisfiable (PosFin 65) f8217 := by
  apply lratCheckerSound f8217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8217
  · intro a ha; simp [p8217] at ha; subst a; trivial
  · exact checked8217
theorem derived8217 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8217 := by
  apply localUnsat_implies_entails f8217 [c8124, c445, c638, c2008] c8217 unsat8217 (by rfl) a
  have h0 : Entails.eval a c8124 := derived8124 a h
  have h1 : Entails.eval a c445 := h 444 (by decide)
  have h2 : Entails.eval a c638 := h 637 (by decide)
  have h3 : Entails.eval a c2008 := h 2007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8218 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8218 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8217, some c8214, some c8124, some c642, some c2458, some c2104, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8218 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8218 : lratChecker f8218 p8218 = .success := by decide +kernel
theorem unsat8218 : Unsatisfiable (PosFin 65) f8218 := by
  apply lratCheckerSound f8218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8218
  · intro a ha; simp [p8218] at ha; subst a; trivial
  · exact checked8218
theorem derived8218 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8218 := by
  apply localUnsat_implies_entails f8218 [c8217, c8214, c8124, c642, c2458, c2104] c8218 unsat8218 (by rfl) a
  have h0 : Entails.eval a c8217 := derived8217 a h
  have h1 : Entails.eval a c8214 := derived8214 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c642 := h 641 (by decide)
  have h4 : Entails.eval a c2458 := h 2457 (by decide)
  have h5 : Entails.eval a c2104 := h 2103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8219 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8219 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8217, some c8214, some c8124, some c8218, some c2013, some c1982, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8219 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8219 : lratChecker f8219 p8219 = .success := by decide +kernel
theorem unsat8219 : Unsatisfiable (PosFin 65) f8219 := by
  apply lratCheckerSound f8219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8219
  · intro a ha; simp [p8219] at ha; subst a; trivial
  · exact checked8219
theorem derived8219 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8219 := by
  apply localUnsat_implies_entails f8219 [c8217, c8214, c8124, c8218, c2013, c1982] c8219 unsat8219 (by rfl) a
  have h0 : Entails.eval a c8217 := derived8217 a h
  have h1 : Entails.eval a c8214 := derived8214 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c8218 := derived8218 a h
  have h4 : Entails.eval a c2013 := h 2012 (by decide)
  have h5 : Entails.eval a c1982 := h 1981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8220 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8220 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8217, some c8214, some c8124, some c642, some c8164, some c2462, some c2107, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8220 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8220 : lratChecker f8220 p8220 = .success := by decide +kernel
theorem unsat8220 : Unsatisfiable (PosFin 65) f8220 := by
  apply lratCheckerSound f8220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8220
  · intro a ha; simp [p8220] at ha; subst a; trivial
  · exact checked8220
theorem derived8220 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8220 := by
  apply localUnsat_implies_entails f8220 [c8217, c8214, c8124, c642, c8164, c2462, c2107] c8220 unsat8220 (by rfl) a
  have h0 : Entails.eval a c8217 := derived8217 a h
  have h1 : Entails.eval a c8214 := derived8214 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c642 := h 641 (by decide)
  have h4 : Entails.eval a c8164 := derived8164 a h
  have h5 : Entails.eval a c2462 := h 2461 (by decide)
  have h6 : Entails.eval a c2107 := h 2106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8221 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8221 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8206, some c8124, some c8216, some c8217, some c8214, some c8219, some c8220, some c2013, some c2006, some c1985, some c1999, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8221 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8221 : lratChecker f8221 p8221 = .success := by decide +kernel
theorem unsat8221 : Unsatisfiable (PosFin 65) f8221 := by
  apply lratCheckerSound f8221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8221
  · intro a ha; simp [p8221] at ha; subst a; trivial
  · exact checked8221
theorem derived8221 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8221 := by
  apply localUnsat_implies_entails f8221 [c7849, c8206, c8124, c8216, c8217, c8214, c8219, c8220, c2013, c2006, c1985, c1999] c8221 unsat8221 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8206 := derived8206 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c8216 := derived8216 a h
  have h4 : Entails.eval a c8217 := derived8217 a h
  have h5 : Entails.eval a c8214 := derived8214 a h
  have h6 : Entails.eval a c8219 := derived8219 a h
  have h7 : Entails.eval a c8220 := derived8220 a h
  have h8 : Entails.eval a c2013 := h 2012 (by decide)
  have h9 : Entails.eval a c2006 := h 2005 (by decide)
  have h10 : Entails.eval a c1985 := h 1984 (by decide)
  have h11 : Entails.eval a c1999 := h 1998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8222 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8222 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c533, some c554, some c8116, some c1024, some c529, some c551, some c544, some c541, some c8208, some c1244, some c1701, some c7275, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8222 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8222 : lratChecker f8222 p8222 = .success := by decide +kernel
theorem unsat8222 : Unsatisfiable (PosFin 65) f8222 := by
  apply lratCheckerSound f8222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8222
  · intro a ha; simp [p8222] at ha; subst a; trivial
  · exact checked8222
theorem derived8222 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8222 := by
  apply localUnsat_implies_entails f8222 [c533, c554, c8116, c1024, c529, c551, c544, c541, c8208, c1244, c1701, c7275] c8222 unsat8222 (by rfl) a
  have h0 : Entails.eval a c533 := h 532 (by decide)
  have h1 : Entails.eval a c554 := h 553 (by decide)
  have h2 : Entails.eval a c8116 := derived8116 a h
  have h3 : Entails.eval a c1024 := h 1023 (by decide)
  have h4 : Entails.eval a c529 := h 528 (by decide)
  have h5 : Entails.eval a c551 := h 550 (by decide)
  have h6 : Entails.eval a c544 := h 543 (by decide)
  have h7 : Entails.eval a c541 := h 540 (by decide)
  have h8 : Entails.eval a c8208 := derived8208 a h
  have h9 : Entails.eval a c1244 := h 1243 (by decide)
  have h10 : Entails.eval a c1701 := h 1700 (by decide)
  have h11 : Entails.eval a c7275 := derived7275 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8223 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8223 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8222, some c2247, some c678, some c692, some c677, some c684, some c582, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8223 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8223 : lratChecker f8223 p8223 = .success := by decide +kernel
theorem unsat8223 : Unsatisfiable (PosFin 65) f8223 := by
  apply lratCheckerSound f8223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8223
  · intro a ha; simp [p8223] at ha; subst a; trivial
  · exact checked8223
theorem derived8223 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8223 := by
  apply localUnsat_implies_entails f8223 [c8222, c2247, c678, c692, c677, c684, c582] c8223 unsat8223 (by rfl) a
  have h0 : Entails.eval a c8222 := derived8222 a h
  have h1 : Entails.eval a c2247 := h 2246 (by decide)
  have h2 : Entails.eval a c678 := h 677 (by decide)
  have h3 : Entails.eval a c692 := h 691 (by decide)
  have h4 : Entails.eval a c677 := h 676 (by decide)
  have h5 : Entails.eval a c684 := h 683 (by decide)
  have h6 : Entails.eval a c582 := h 581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8224 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8224 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1024, some c2277, some c1036, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8224 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8224 : lratChecker f8224 p8224 = .success := by decide +kernel
theorem unsat8224 : Unsatisfiable (PosFin 65) f8224 := by
  apply lratCheckerSound f8224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8224
  · intro a ha; simp [p8224] at ha; subst a; trivial
  · exact checked8224
theorem derived8224 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8224 := by
  apply localUnsat_implies_entails f8224 [c1024, c2277, c1036] c8224 unsat8224 (by rfl) a
  have h0 : Entails.eval a c1024 := h 1023 (by decide)
  have h1 : Entails.eval a c2277 := h 2276 (by decide)
  have h2 : Entails.eval a c1036 := h 1035 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8225 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8225 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8223, some c8224, some c2247, some c678, some c692, some c677, some c682, some c684, some c689, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8225 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8225 : lratChecker f8225 p8225 = .success := by decide +kernel
theorem unsat8225 : Unsatisfiable (PosFin 65) f8225 := by
  apply lratCheckerSound f8225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8225
  · intro a ha; simp [p8225] at ha; subst a; trivial
  · exact checked8225
theorem derived8225 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8225 := by
  apply localUnsat_implies_entails f8225 [c8223, c8224, c2247, c678, c692, c677, c682, c684, c689] c8225 unsat8225 (by rfl) a
  have h0 : Entails.eval a c8223 := derived8223 a h
  have h1 : Entails.eval a c8224 := derived8224 a h
  have h2 : Entails.eval a c2247 := h 2246 (by decide)
  have h3 : Entails.eval a c678 := h 677 (by decide)
  have h4 : Entails.eval a c692 := h 691 (by decide)
  have h5 : Entails.eval a c677 := h 676 (by decide)
  have h6 : Entails.eval a c682 := h 681 (by decide)
  have h7 : Entails.eval a c684 := h 683 (by decide)
  have h8 : Entails.eval a c689 := h 688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8226 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8226 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c555, some c8172, some c8103, some c683, some c609, some c2577, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8226 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8226 : lratChecker f8226 p8226 = .success := by decide +kernel
theorem unsat8226 : Unsatisfiable (PosFin 65) f8226 := by
  apply lratCheckerSound f8226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8226
  · intro a ha; simp [p8226] at ha; subst a; trivial
  · exact checked8226
theorem derived8226 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8226 := by
  apply localUnsat_implies_entails f8226 [c555, c8172, c8103, c683, c609, c2577] c8226 unsat8226 (by rfl) a
  have h0 : Entails.eval a c555 := h 554 (by decide)
  have h1 : Entails.eval a c8172 := derived8172 a h
  have h2 : Entails.eval a c8103 := derived8103 a h
  have h3 : Entails.eval a c683 := h 682 (by decide)
  have h4 : Entails.eval a c609 := h 608 (by decide)
  have h5 : Entails.eval a c2577 := h 2576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8227 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8227 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2370, some c2084, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8227 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8227 : lratChecker f8227 p8227 = .success := by decide +kernel
theorem unsat8227 : Unsatisfiable (PosFin 65) f8227 := by
  apply lratCheckerSound f8227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8227
  · intro a ha; simp [p8227] at ha; subst a; trivial
  · exact checked8227
theorem derived8227 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8227 := by
  apply localUnsat_implies_entails f8227 [c2370, c2084] c8227 unsat8227 (by rfl) a
  have h0 : Entails.eval a c2370 := h 2369 (by decide)
  have h1 : Entails.eval a c2084 := h 2083 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8228 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8228 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8227, some c2383, some c465, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8228 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8228 : lratChecker f8228 p8228 = .success := by decide +kernel
theorem unsat8228 : Unsatisfiable (PosFin 65) f8228 := by
  apply lratCheckerSound f8228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8228
  · intro a ha; simp [p8228] at ha; subst a; trivial
  · exact checked8228
theorem derived8228 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8228 := by
  apply localUnsat_implies_entails f8228 [c8227, c2383, c465] c8228 unsat8228 (by rfl) a
  have h0 : Entails.eval a c8227 := derived8227 a h
  have h1 : Entails.eval a c2383 := h 2382 (by decide)
  have h2 : Entails.eval a c465 := h 464 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8229 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8229 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2370, some c120, some c8200, some c2642, some c1245, some c155, some c1785, some c2977, some c149, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8229 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8229 : lratChecker f8229 p8229 = .success := by decide +kernel
theorem unsat8229 : Unsatisfiable (PosFin 65) f8229 := by
  apply lratCheckerSound f8229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8229
  · intro a ha; simp [p8229] at ha; subst a; trivial
  · exact checked8229
theorem derived8229 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8229 := by
  apply localUnsat_implies_entails f8229 [c2370, c120, c8200, c2642, c1245, c155, c1785, c2977, c149] c8229 unsat8229 (by rfl) a
  have h0 : Entails.eval a c2370 := h 2369 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c8200 := derived8200 a h
  have h3 : Entails.eval a c2642 := h 2641 (by decide)
  have h4 : Entails.eval a c1245 := h 1244 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c1785 := h 1784 (by decide)
  have h7 : Entails.eval a c2977 := h 2976 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8230 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8230 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8228, some c8229, some c591, some c121, some c157, some c6754, some c3168, some c6755, some c3167, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8230 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8230 : lratChecker f8230 p8230 = .success := by decide +kernel
theorem unsat8230 : Unsatisfiable (PosFin 65) f8230 := by
  apply lratCheckerSound f8230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8230
  · intro a ha; simp [p8230] at ha; subst a; trivial
  · exact checked8230
theorem derived8230 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8230 := by
  apply localUnsat_implies_entails f8230 [c8228, c8229, c591, c121, c157, c6754, c3168, c6755, c3167] c8230 unsat8230 (by rfl) a
  have h0 : Entails.eval a c8228 := derived8228 a h
  have h1 : Entails.eval a c8229 := derived8229 a h
  have h2 : Entails.eval a c591 := h 590 (by decide)
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c6754 := derived6754 a h
  have h6 : Entails.eval a c3168 := h 3167 (by decide)
  have h7 : Entails.eval a c6755 := derived6755 a h
  have h8 : Entails.eval a c3167 := h 3166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8231 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8231 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2096, some c2087, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8231 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8231 : lratChecker f8231 p8231 = .success := by decide +kernel
theorem unsat8231 : Unsatisfiable (PosFin 65) f8231 := by
  apply lratCheckerSound f8231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8231
  · intro a ha; simp [p8231] at ha; subst a; trivial
  · exact checked8231
theorem derived8231 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8231 := by
  apply localUnsat_implies_entails f8231 [c2096, c2087] c8231 unsat8231 (by rfl) a
  have h0 : Entails.eval a c2096 := h 2095 (by decide)
  have h1 : Entails.eval a c2087 := h 2086 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8232 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8232 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8227, some c8231, some c2393, some c2401, some c2382, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8232 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8232 : lratChecker f8232 p8232 = .success := by decide +kernel
theorem unsat8232 : Unsatisfiable (PosFin 65) f8232 := by
  apply lratCheckerSound f8232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8232
  · intro a ha; simp [p8232] at ha; subst a; trivial
  · exact checked8232
theorem derived8232 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8232 := by
  apply localUnsat_implies_entails f8232 [c8227, c8231, c2393, c2401, c2382] c8232 unsat8232 (by rfl) a
  have h0 : Entails.eval a c8227 := derived8227 a h
  have h1 : Entails.eval a c8231 := derived8231 a h
  have h2 : Entails.eval a c2393 := h 2392 (by decide)
  have h3 : Entails.eval a c2401 := h 2400 (by decide)
  have h4 : Entails.eval a c2382 := h 2381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8233 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8233 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1958, some c693, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8233 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8233 : lratChecker f8233 p8233 = .success := by decide +kernel
theorem unsat8233 : Unsatisfiable (PosFin 65) f8233 := by
  apply lratCheckerSound f8233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8233
  · intro a ha; simp [p8233] at ha; subst a; trivial
  · exact checked8233
theorem derived8233 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8233 := by
  apply localUnsat_implies_entails f8233 [c1958, c693] c8233 unsat8233 (by rfl) a
  have h0 : Entails.eval a c1958 := h 1957 (by decide)
  have h1 : Entails.eval a c693 := h 692 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8234 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨28, by decide⟩, true), (⟨7, by decide⟩, true), (⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8234 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c578, some c582, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8234 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8234 : lratChecker f8234 p8234 = .success := by decide +kernel
theorem unsat8234 : Unsatisfiable (PosFin 65) f8234 := by
  apply lratCheckerSound f8234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8234
  · intro a ha; simp [p8234] at ha; subst a; trivial
  · exact checked8234
theorem derived8234 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8234 := by
  apply localUnsat_implies_entails f8234 [c578, c582] c8234 unsat8234 (by rfl) a
  have h0 : Entails.eval a c578 := h 577 (by decide)
  have h1 : Entails.eval a c582 := h 581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8235 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8235 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8225, some c8226, some c8230, some c8232, some c8233, some c8234, some c2244, some c2262, some c1937, some c2257, some c2248, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8235 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8235 : lratChecker f8235 p8235 = .success := by decide +kernel
theorem unsat8235 : Unsatisfiable (PosFin 65) f8235 := by
  apply lratCheckerSound f8235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8235
  · intro a ha; simp [p8235] at ha; subst a; trivial
  · exact checked8235
theorem derived8235 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8235 := by
  apply localUnsat_implies_entails f8235 [c8225, c8226, c8230, c8232, c8233, c8234, c2244, c2262, c1937, c2257, c2248] c8235 unsat8235 (by rfl) a
  have h0 : Entails.eval a c8225 := derived8225 a h
  have h1 : Entails.eval a c8226 := derived8226 a h
  have h2 : Entails.eval a c8230 := derived8230 a h
  have h3 : Entails.eval a c8232 := derived8232 a h
  have h4 : Entails.eval a c8233 := derived8233 a h
  have h5 : Entails.eval a c8234 := derived8234 a h
  have h6 : Entails.eval a c2244 := h 2243 (by decide)
  have h7 : Entails.eval a c2262 := h 2261 (by decide)
  have h8 : Entails.eval a c1937 := h 1936 (by decide)
  have h9 : Entails.eval a c2257 := h 2256 (by decide)
  have h10 : Entails.eval a c2248 := h 2247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8236 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8236 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c555, some c8172, some c8103, some c683, some c2574, some c513, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8236 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8236 : lratChecker f8236 p8236 = .success := by decide +kernel
theorem unsat8236 : Unsatisfiable (PosFin 65) f8236 := by
  apply lratCheckerSound f8236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8236
  · intro a ha; simp [p8236] at ha; subst a; trivial
  · exact checked8236
theorem derived8236 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8236 := by
  apply localUnsat_implies_entails f8236 [c555, c8172, c8103, c683, c2574, c513] c8236 unsat8236 (by rfl) a
  have h0 : Entails.eval a c555 := h 554 (by decide)
  have h1 : Entails.eval a c8172 := derived8172 a h
  have h2 : Entails.eval a c8103 := derived8103 a h
  have h3 : Entails.eval a c683 := h 682 (by decide)
  have h4 : Entails.eval a c2574 := h 2573 (by decide)
  have h5 : Entails.eval a c513 := h 512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8237 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8237 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8228, some c8232, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8237 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8237 : lratChecker f8237 p8237 = .success := by decide +kernel
theorem unsat8237 : Unsatisfiable (PosFin 65) f8237 := by
  apply lratCheckerSound f8237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8237
  · intro a ha; simp [p8237] at ha; subst a; trivial
  · exact checked8237
theorem derived8237 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8237 := by
  apply localUnsat_implies_entails f8237 [c8228, c8232] c8237 unsat8237 (by rfl) a
  have h0 : Entails.eval a c8228 := derived8228 a h
  have h1 : Entails.eval a c8232 := derived8232 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8238 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8238 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8225, some c8235, some c8236, some c8237, some c1925, some c1893, some c1897, some c1922, some c1908, some c686, some c2244, some c1937, some c2257, some c2248, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8238 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8238 : lratChecker f8238 p8238 = .success := by decide +kernel
theorem unsat8238 : Unsatisfiable (PosFin 65) f8238 := by
  apply lratCheckerSound f8238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8238
  · intro a ha; simp [p8238] at ha; subst a; trivial
  · exact checked8238
theorem derived8238 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8238 := by
  apply localUnsat_implies_entails f8238 [c8225, c8235, c8236, c8237, c1925, c1893, c1897, c1922, c1908, c686, c2244, c1937, c2257, c2248] c8238 unsat8238 (by rfl) a
  have h0 : Entails.eval a c8225 := derived8225 a h
  have h1 : Entails.eval a c8235 := derived8235 a h
  have h2 : Entails.eval a c8236 := derived8236 a h
  have h3 : Entails.eval a c8237 := derived8237 a h
  have h4 : Entails.eval a c1925 := h 1924 (by decide)
  have h5 : Entails.eval a c1893 := h 1892 (by decide)
  have h6 : Entails.eval a c1897 := h 1896 (by decide)
  have h7 : Entails.eval a c1922 := h 1921 (by decide)
  have h8 : Entails.eval a c1908 := h 1907 (by decide)
  have h9 : Entails.eval a c686 := h 685 (by decide)
  have h10 : Entails.eval a c2244 := h 2243 (by decide)
  have h11 : Entails.eval a c1937 := h 1936 (by decide)
  have h12 : Entails.eval a c2257 := h 2256 (by decide)
  have h13 : Entails.eval a c2248 := h 2247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8239 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨31, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8239 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6737, some c6738, some c3013, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8239 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8239 : lratChecker f8239 p8239 = .success := by decide +kernel
theorem unsat8239 : Unsatisfiable (PosFin 65) f8239 := by
  apply lratCheckerSound f8239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8239
  · intro a ha; simp [p8239] at ha; subst a; trivial
  · exact checked8239
theorem derived8239 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8239 := by
  apply localUnsat_implies_entails f8239 [c6737, c6738, c3013] c8239 unsat8239 (by rfl) a
  have h0 : Entails.eval a c6737 := derived6737 a h
  have h1 : Entails.eval a c6738 := derived6738 a h
  have h2 : Entails.eval a c3013 := h 3012 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8240 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8240 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c8212, some c8239, some c3015, some c3014, some c3012, some c3017, some c117, some c172, some c1576, some c1736, some c1308, some c1935, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8240 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8240 : lratChecker f8240 p8240 = .success := by decide +kernel
theorem unsat8240 : Unsatisfiable (PosFin 65) f8240 := by
  apply lratCheckerSound f8240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8240
  · intro a ha; simp [p8240] at ha; subst a; trivial
  · exact checked8240
theorem derived8240 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8240 := by
  apply localUnsat_implies_entails f8240 [c8159, c8212, c8239, c3015, c3014, c3012, c3017, c117, c172, c1576, c1736, c1308, c1935] c8240 unsat8240 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c8212 := derived8212 a h
  have h2 : Entails.eval a c8239 := derived8239 a h
  have h3 : Entails.eval a c3015 := h 3014 (by decide)
  have h4 : Entails.eval a c3014 := h 3013 (by decide)
  have h5 : Entails.eval a c3012 := h 3011 (by decide)
  have h6 : Entails.eval a c3017 := h 3016 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c1576 := h 1575 (by decide)
  have h10 : Entails.eval a c1736 := h 1735 (by decide)
  have h11 : Entails.eval a c1308 := h 1307 (by decide)
  have h12 : Entails.eval a c1935 := h 1934 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8241 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨15, by decide⟩, false), (⟨17, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8241 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7874, some c1202, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8241 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8241 : lratChecker f8241 p8241 = .success := by decide +kernel
theorem unsat8241 : Unsatisfiable (PosFin 65) f8241 := by
  apply lratCheckerSound f8241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8241
  · intro a ha; simp [p8241] at ha; subst a; trivial
  · exact checked8241
theorem derived8241 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8241 := by
  apply localUnsat_implies_entails f8241 [c7874, c1202] c8241 unsat8241 (by rfl) a
  have h0 : Entails.eval a c7874 := derived7874 a h
  have h1 : Entails.eval a c1202 := h 1201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8242 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8242 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8231, some c8241, some c1277, some c1293, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8242 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8242 : lratChecker f8242 p8242 = .success := by decide +kernel
theorem unsat8242 : Unsatisfiable (PosFin 65) f8242 := by
  apply lratCheckerSound f8242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8242
  · intro a ha; simp [p8242] at ha; subst a; trivial
  · exact checked8242
theorem derived8242 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8242 := by
  apply localUnsat_implies_entails f8242 [c8231, c8241, c1277, c1293] c8242 unsat8242 (by rfl) a
  have h0 : Entails.eval a c8231 := derived8231 a h
  have h1 : Entails.eval a c8241 := derived8241 a h
  have h2 : Entails.eval a c1277 := h 1276 (by decide)
  have h3 : Entails.eval a c1293 := h 1292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8243 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨31, by decide⟩, false), (⟨16, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8243 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8175, some c8011, some c8208, some c8242, some c8030, some c1309, some c1332, some c1097, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8243 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8243 : lratChecker f8243 p8243 = .success := by decide +kernel
theorem unsat8243 : Unsatisfiable (PosFin 65) f8243 := by
  apply lratCheckerSound f8243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8243
  · intro a ha; simp [p8243] at ha; subst a; trivial
  · exact checked8243
theorem derived8243 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8243 := by
  apply localUnsat_implies_entails f8243 [c8175, c8011, c8208, c8242, c8030, c1309, c1332, c1097] c8243 unsat8243 (by rfl) a
  have h0 : Entails.eval a c8175 := derived8175 a h
  have h1 : Entails.eval a c8011 := derived8011 a h
  have h2 : Entails.eval a c8208 := derived8208 a h
  have h3 : Entails.eval a c8242 := derived8242 a h
  have h4 : Entails.eval a c8030 := derived8030 a h
  have h5 : Entails.eval a c1309 := h 1308 (by decide)
  have h6 : Entails.eval a c1332 := h 1331 (by decide)
  have h7 : Entails.eval a c1097 := h 1096 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8244 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8244 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8221, some c8159, some c7849, some c7941, some c8238, some c8240, some c8175, some c8243, some c8201, some c8237, some c8030, some c1936, some c1897, some c577, some c582, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8244 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8244 : lratChecker f8244 p8244 = .success := by decide +kernel
theorem unsat8244 : Unsatisfiable (PosFin 65) f8244 := by
  apply lratCheckerSound f8244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8244
  · intro a ha; simp [p8244] at ha; subst a; trivial
  · exact checked8244
theorem derived8244 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8244 := by
  apply localUnsat_implies_entails f8244 [c8221, c8159, c7849, c7941, c8238, c8240, c8175, c8243, c8201, c8237, c8030, c1936, c1897, c577, c582] c8244 unsat8244 (by rfl) a
  have h0 : Entails.eval a c8221 := derived8221 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c7941 := derived7941 a h
  have h4 : Entails.eval a c8238 := derived8238 a h
  have h5 : Entails.eval a c8240 := derived8240 a h
  have h6 : Entails.eval a c8175 := derived8175 a h
  have h7 : Entails.eval a c8243 := derived8243 a h
  have h8 : Entails.eval a c8201 := derived8201 a h
  have h9 : Entails.eval a c8237 := derived8237 a h
  have h10 : Entails.eval a c8030 := derived8030 a h
  have h11 : Entails.eval a c1936 := h 1935 (by decide)
  have h12 : Entails.eval a c1897 := h 1896 (by decide)
  have h13 : Entails.eval a c577 := h 576 (by decide)
  have h14 : Entails.eval a c582 := h 581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8245 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8245 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8118, some c554, some c8116, some c1246, some c1394, some c1735, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8245 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8245 : lratChecker f8245 p8245 = .success := by decide +kernel
theorem unsat8245 : Unsatisfiable (PosFin 65) f8245 := by
  apply lratCheckerSound f8245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8245
  · intro a ha; simp [p8245] at ha; subst a; trivial
  · exact checked8245
theorem derived8245 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8245 := by
  apply localUnsat_implies_entails f8245 [c8118, c554, c8116, c1246, c1394, c1735] c8245 unsat8245 (by rfl) a
  have h0 : Entails.eval a c8118 := derived8118 a h
  have h1 : Entails.eval a c554 := h 553 (by decide)
  have h2 : Entails.eval a c8116 := derived8116 a h
  have h3 : Entails.eval a c1246 := h 1245 (by decide)
  have h4 : Entails.eval a c1394 := h 1393 (by decide)
  have h5 : Entails.eval a c1735 := h 1734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8246 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8246 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8245, some c8236, some c555, some c8172, some c8103, some c522, some c7565, some c7375, some c8015, some c1249, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8246 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8246 : lratChecker f8246 p8246 = .success := by decide +kernel
theorem unsat8246 : Unsatisfiable (PosFin 65) f8246 := by
  apply lratCheckerSound f8246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8246
  · intro a ha; simp [p8246] at ha; subst a; trivial
  · exact checked8246
theorem derived8246 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8246 := by
  apply localUnsat_implies_entails f8246 [c8245, c8236, c555, c8172, c8103, c522, c7565, c7375, c8015, c1249] c8246 unsat8246 (by rfl) a
  have h0 : Entails.eval a c8245 := derived8245 a h
  have h1 : Entails.eval a c8236 := derived8236 a h
  have h2 : Entails.eval a c555 := h 554 (by decide)
  have h3 : Entails.eval a c8172 := derived8172 a h
  have h4 : Entails.eval a c8103 := derived8103 a h
  have h5 : Entails.eval a c522 := h 521 (by decide)
  have h6 : Entails.eval a c7565 := derived7565 a h
  have h7 : Entails.eval a c7375 := derived7375 a h
  have h8 : Entails.eval a c8015 := derived8015 a h
  have h9 : Entails.eval a c1249 := h 1248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8247 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8247 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2255, some c678, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8247 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8247 : lratChecker f8247 p8247 = .success := by decide +kernel
theorem unsat8247 : Unsatisfiable (PosFin 65) f8247 := by
  apply lratCheckerSound f8247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8247
  · intro a ha; simp [p8247] at ha; subst a; trivial
  · exact checked8247
theorem derived8247 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8247 := by
  apply localUnsat_implies_entails f8247 [c2255, c678] c8247 unsat8247 (by rfl) a
  have h0 : Entails.eval a c2255 := h 2254 (by decide)
  have h1 : Entails.eval a c678 := h 677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8248 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8248 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2368, some c2242, some c2523, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8248 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8248 : lratChecker f8248 p8248 = .success := by decide +kernel
theorem unsat8248 : Unsatisfiable (PosFin 65) f8248 := by
  apply lratCheckerSound f8248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8248
  · intro a ha; simp [p8248] at ha; subst a; trivial
  · exact checked8248
theorem derived8248 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8248 := by
  apply localUnsat_implies_entails f8248 [c2368, c2242, c2523] c8248 unsat8248 (by rfl) a
  have h0 : Entails.eval a c2368 := h 2367 (by decide)
  have h1 : Entails.eval a c2242 := h 2241 (by decide)
  have h2 : Entails.eval a c2523 := h 2522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8249 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8249 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2245, some c2246, some c2262, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8249 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8249 : lratChecker f8249 p8249 = .success := by decide +kernel
theorem unsat8249 : Unsatisfiable (PosFin 65) f8249 := by
  apply lratCheckerSound f8249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8249
  · intro a ha; simp [p8249] at ha; subst a; trivial
  · exact checked8249
theorem derived8249 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8249 := by
  apply localUnsat_implies_entails f8249 [c2245, c2246, c2262] c8249 unsat8249 (by rfl) a
  have h0 : Entails.eval a c2245 := h 2244 (by decide)
  have h1 : Entails.eval a c2246 := h 2245 (by decide)
  have h2 : Entails.eval a c2262 := h 2261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8250 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8250 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8246, some c8248, some c8247, some c8249, some c693, some c675, some c679, some c674, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8250 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8250 : lratChecker f8250 p8250 = .success := by decide +kernel
theorem unsat8250 : Unsatisfiable (PosFin 65) f8250 := by
  apply lratCheckerSound f8250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8250
  · intro a ha; simp [p8250] at ha; subst a; trivial
  · exact checked8250
theorem derived8250 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8250 := by
  apply localUnsat_implies_entails f8250 [c8246, c8248, c8247, c8249, c693, c675, c679, c674] c8250 unsat8250 (by rfl) a
  have h0 : Entails.eval a c8246 := derived8246 a h
  have h1 : Entails.eval a c8248 := derived8248 a h
  have h2 : Entails.eval a c8247 := derived8247 a h
  have h3 : Entails.eval a c8249 := derived8249 a h
  have h4 : Entails.eval a c693 := h 692 (by decide)
  have h5 : Entails.eval a c675 := h 674 (by decide)
  have h6 : Entails.eval a c679 := h 678 (by decide)
  have h7 : Entails.eval a c674 := h 673 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8251 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8251 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1567, some c2080, some c1866, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8251 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8251 : lratChecker f8251 p8251 = .success := by decide +kernel
theorem unsat8251 : Unsatisfiable (PosFin 65) f8251 := by
  apply lratCheckerSound f8251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8251
  · intro a ha; simp [p8251] at ha; subst a; trivial
  · exact checked8251
theorem derived8251 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8251 := by
  apply localUnsat_implies_entails f8251 [c1567, c2080, c1866] c8251 unsat8251 (by rfl) a
  have h0 : Entails.eval a c1567 := h 1566 (by decide)
  have h1 : Entails.eval a c2080 := h 2079 (by decide)
  have h2 : Entails.eval a c1866 := h 1865 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8252 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8252 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8188, some c1259, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8252 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8252 : lratChecker f8252 p8252 = .success := by decide +kernel
theorem unsat8252 : Unsatisfiable (PosFin 65) f8252 := by
  apply lratCheckerSound f8252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8252
  · intro a ha; simp [p8252] at ha; subst a; trivial
  · exact checked8252
theorem derived8252 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8252 := by
  apply localUnsat_implies_entails f8252 [c8188, c1259] c8252 unsat8252 (by rfl) a
  have h0 : Entails.eval a c8188 := derived8188 a h
  have h1 : Entails.eval a c1259 := h 1258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8253 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8253 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c7849, some c8251, some c1594, some c8252, some c497, some c1844, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8253 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8253 : lratChecker f8253 p8253 = .success := by decide +kernel
theorem unsat8253 : Unsatisfiable (PosFin 65) f8253 := by
  apply lratCheckerSound f8253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8253
  · intro a ha; simp [p8253] at ha; subst a; trivial
  · exact checked8253
theorem derived8253 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8253 := by
  apply localUnsat_implies_entails f8253 [c8159, c7849, c8251, c1594, c8252, c497, c1844] c8253 unsat8253 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8251 := derived8251 a h
  have h3 : Entails.eval a c1594 := h 1593 (by decide)
  have h4 : Entails.eval a c8252 := derived8252 a h
  have h5 : Entails.eval a c497 := h 496 (by decide)
  have h6 : Entails.eval a c1844 := h 1843 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8254 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8254 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1983, some c2142, some c2638, some c495, some c509, some c586, some c510, some c2349, some c2657, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8254 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8254 : lratChecker f8254 p8254 = .success := by decide +kernel
theorem unsat8254 : Unsatisfiable (PosFin 65) f8254 := by
  apply lratCheckerSound f8254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8254
  · intro a ha; simp [p8254] at ha; subst a; trivial
  · exact checked8254
theorem derived8254 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8254 := by
  apply localUnsat_implies_entails f8254 [c1983, c2142, c2638, c495, c509, c586, c510, c2349, c2657] c8254 unsat8254 (by rfl) a
  have h0 : Entails.eval a c1983 := h 1982 (by decide)
  have h1 : Entails.eval a c2142 := h 2141 (by decide)
  have h2 : Entails.eval a c2638 := h 2637 (by decide)
  have h3 : Entails.eval a c495 := h 494 (by decide)
  have h4 : Entails.eval a c509 := h 508 (by decide)
  have h5 : Entails.eval a c586 := h 585 (by decide)
  have h6 : Entails.eval a c510 := h 509 (by decide)
  have h7 : Entails.eval a c2349 := h 2348 (by decide)
  have h8 : Entails.eval a c2657 := h 2656 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8255 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8255 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c8221, some c7849, some c8244, some c8250, some c8253, some c8254, some c2118, some c2001, some c1659, some c8152, some c8252, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8255 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8255 : lratChecker f8255 p8255 = .success := by decide +kernel
theorem unsat8255 : Unsatisfiable (PosFin 65) f8255 := by
  apply lratCheckerSound f8255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8255
  · intro a ha; simp [p8255] at ha; subst a; trivial
  · exact checked8255
theorem derived8255 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8255 := by
  apply localUnsat_implies_entails f8255 [c8159, c8221, c7849, c8244, c8250, c8253, c8254, c2118, c2001, c1659, c8152, c8252] c8255 unsat8255 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c8221 := derived8221 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8244 := derived8244 a h
  have h4 : Entails.eval a c8250 := derived8250 a h
  have h5 : Entails.eval a c8253 := derived8253 a h
  have h6 : Entails.eval a c8254 := derived8254 a h
  have h7 : Entails.eval a c2118 := h 2117 (by decide)
  have h8 : Entails.eval a c2001 := h 2000 (by decide)
  have h9 : Entails.eval a c1659 := h 1658 (by decide)
  have h10 : Entails.eval a c8152 := derived8152 a h
  have h11 : Entails.eval a c8252 := derived8252 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8256 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8256 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c975, some c1587, some c2090, some c958, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8256 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8256 : lratChecker f8256 p8256 = .success := by decide +kernel
theorem unsat8256 : Unsatisfiable (PosFin 65) f8256 := by
  apply lratCheckerSound f8256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8256
  · intro a ha; simp [p8256] at ha; subst a; trivial
  · exact checked8256
theorem derived8256 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8256 := by
  apply localUnsat_implies_entails f8256 [c975, c1587, c2090, c958] c8256 unsat8256 (by rfl) a
  have h0 : Entails.eval a c975 := h 974 (by decide)
  have h1 : Entails.eval a c1587 := h 1586 (by decide)
  have h2 : Entails.eval a c2090 := h 2089 (by decide)
  have h3 : Entails.eval a c958 := h 957 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8257 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8257 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1574, some c8252, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8257 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8257 : lratChecker f8257 p8257 = .success := by decide +kernel
theorem unsat8257 : Unsatisfiable (PosFin 65) f8257 := by
  apply lratCheckerSound f8257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8257
  · intro a ha; simp [p8257] at ha; subst a; trivial
  · exact checked8257
theorem derived8257 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8257 := by
  apply localUnsat_implies_entails f8257 [c1574, c8252] c8257 unsat8257 (by rfl) a
  have h0 : Entails.eval a c1574 := h 1573 (by decide)
  have h1 : Entails.eval a c8252 := derived8252 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8258 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨15, by decide⟩, false), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8258 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1879, some c1869, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8258 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8258 : lratChecker f8258 p8258 = .success := by decide +kernel
theorem unsat8258 : Unsatisfiable (PosFin 65) f8258 := by
  apply lratCheckerSound f8258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8258
  · intro a ha; simp [p8258] at ha; subst a; trivial
  · exact checked8258
theorem derived8258 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8258 := by
  apply localUnsat_implies_entails f8258 [c1879, c1869] c8258 unsat8258 (by rfl) a
  have h0 : Entails.eval a c1879 := h 1878 (by decide)
  have h1 : Entails.eval a c1869 := h 1868 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8259 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8259 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8251, some c8257, some c7929, some c8258, some c1575, some c1591, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8259 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8259 : lratChecker f8259 p8259 = .success := by decide +kernel
theorem unsat8259 : Unsatisfiable (PosFin 65) f8259 := by
  apply lratCheckerSound f8259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8259
  · intro a ha; simp [p8259] at ha; subst a; trivial
  · exact checked8259
theorem derived8259 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8259 := by
  apply localUnsat_implies_entails f8259 [c7849, c8251, c8257, c7929, c8258, c1575, c1591] c8259 unsat8259 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8251 := derived8251 a h
  have h2 : Entails.eval a c8257 := derived8257 a h
  have h3 : Entails.eval a c7929 := derived7929 a h
  have h4 : Entails.eval a c8258 := derived8258 a h
  have h5 : Entails.eval a c1575 := h 1574 (by decide)
  have h6 : Entails.eval a c1591 := h 1590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8260 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8260 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1983, some c2142, some c2638, some c514, some c495, some c586, some c1850, some c513, some c2101, some c1650, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8260 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8260 : lratChecker f8260 p8260 = .success := by decide +kernel
theorem unsat8260 : Unsatisfiable (PosFin 65) f8260 := by
  apply lratCheckerSound f8260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8260
  · intro a ha; simp [p8260] at ha; subst a; trivial
  · exact checked8260
theorem derived8260 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8260 := by
  apply localUnsat_implies_entails f8260 [c1983, c2142, c2638, c514, c495, c586, c1850, c513, c2101, c1650] c8260 unsat8260 (by rfl) a
  have h0 : Entails.eval a c1983 := h 1982 (by decide)
  have h1 : Entails.eval a c2142 := h 2141 (by decide)
  have h2 : Entails.eval a c2638 := h 2637 (by decide)
  have h3 : Entails.eval a c514 := h 513 (by decide)
  have h4 : Entails.eval a c495 := h 494 (by decide)
  have h5 : Entails.eval a c586 := h 585 (by decide)
  have h6 : Entails.eval a c1850 := h 1849 (by decide)
  have h7 : Entails.eval a c513 := h 512 (by decide)
  have h8 : Entails.eval a c2101 := h 2100 (by decide)
  have h9 : Entails.eval a c1650 := h 1649 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8261 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8261 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8188, some c2147, some c7976, some c2616, some c1535, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8261 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8261 : lratChecker f8261 p8261 = .success := by decide +kernel
theorem unsat8261 : Unsatisfiable (PosFin 65) f8261 := by
  apply lratCheckerSound f8261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8261
  · intro a ha; simp [p8261] at ha; subst a; trivial
  · exact checked8261
theorem derived8261 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8261 := by
  apply localUnsat_implies_entails f8261 [c7849, c8188, c2147, c7976, c2616, c1535] c8261 unsat8261 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8188 := derived8188 a h
  have h2 : Entails.eval a c2147 := h 2146 (by decide)
  have h3 : Entails.eval a c7976 := derived7976 a h
  have h4 : Entails.eval a c2616 := h 2615 (by decide)
  have h5 : Entails.eval a c1535 := h 1534 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8262 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8262 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1997, some c602, some c2159, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8262 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8262 : lratChecker f8262 p8262 = .success := by decide +kernel
theorem unsat8262 : Unsatisfiable (PosFin 65) f8262 := by
  apply lratCheckerSound f8262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8262
  · intro a ha; simp [p8262] at ha; subst a; trivial
  · exact checked8262
theorem derived8262 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8262 := by
  apply localUnsat_implies_entails f8262 [c1997, c602, c2159] c8262 unsat8262 (by rfl) a
  have h0 : Entails.eval a c1997 := h 1996 (by decide)
  have h1 : Entails.eval a c602 := h 601 (by decide)
  have h2 : Entails.eval a c2159 := h 2158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8263 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨31, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8263 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2162, some c2174, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p8263 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8263 : lratChecker f8263 p8263 = .success := by decide +kernel
theorem unsat8263 : Unsatisfiable (PosFin 65) f8263 := by
  apply lratCheckerSound f8263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8263
  · intro a ha; simp [p8263] at ha; subst a; trivial
  · exact checked8263
theorem derived8263 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8263 := by
  apply localUnsat_implies_entails f8263 [c2162, c2174] c8263 unsat8263 (by rfl) a
  have h0 : Entails.eval a c2162 := h 2161 (by decide)
  have h1 : Entails.eval a c2174 := h 2173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8264 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8264 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c8221, some c7849, some c8244, some c8250, some c8255, some c8259, some c8260, some c8261, some c8262, some c8263, some c514, some c496, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8264 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8264 : lratChecker f8264 p8264 = .success := by decide +kernel
theorem unsat8264 : Unsatisfiable (PosFin 65) f8264 := by
  apply lratCheckerSound f8264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8264
  · intro a ha; simp [p8264] at ha; subst a; trivial
  · exact checked8264
theorem derived8264 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8264 := by
  apply localUnsat_implies_entails f8264 [c8159, c8221, c7849, c8244, c8250, c8255, c8259, c8260, c8261, c8262, c8263, c514, c496] c8264 unsat8264 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c8221 := derived8221 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8244 := derived8244 a h
  have h4 : Entails.eval a c8250 := derived8250 a h
  have h5 : Entails.eval a c8255 := derived8255 a h
  have h6 : Entails.eval a c8259 := derived8259 a h
  have h7 : Entails.eval a c8260 := derived8260 a h
  have h8 : Entails.eval a c8261 := derived8261 a h
  have h9 : Entails.eval a c8262 := derived8262 a h
  have h10 : Entails.eval a c8263 := derived8263 a h
  have h11 : Entails.eval a c514 := h 513 (by decide)
  have h12 : Entails.eval a c496 := h 495 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8265 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8265 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2372, some c2085, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8265 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8265 : lratChecker f8265 p8265 = .success := by decide +kernel
theorem unsat8265 : Unsatisfiable (PosFin 65) f8265 := by
  apply lratCheckerSound f8265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8265
  · intro a ha; simp [p8265] at ha; subst a; trivial
  · exact checked8265
theorem derived8265 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8265 := by
  apply localUnsat_implies_entails f8265 [c2372, c2085] c8265 unsat8265 (by rfl) a
  have h0 : Entails.eval a c2372 := h 2371 (by decide)
  have h1 : Entails.eval a c2085 := h 2084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8266 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8266 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8248, some c8265, some c7929, some c2374, some c2384, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8266 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8266 : lratChecker f8266 p8266 = .success := by decide +kernel
theorem unsat8266 : Unsatisfiable (PosFin 65) f8266 := by
  apply lratCheckerSound f8266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8266
  · intro a ha; simp [p8266] at ha; subst a; trivial
  · exact checked8266
theorem derived8266 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8266 := by
  apply localUnsat_implies_entails f8266 [c8248, c8265, c7929, c2374, c2384] c8266 unsat8266 (by rfl) a
  have h0 : Entails.eval a c8248 := derived8248 a h
  have h1 : Entails.eval a c8265 := derived8265 a h
  have h2 : Entails.eval a c7929 := derived7929 a h
  have h3 : Entails.eval a c2374 := h 2373 (by decide)
  have h4 : Entails.eval a c2384 := h 2383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8267 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8267 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2372, some c2147, some c2643, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8267 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8267 : lratChecker f8267 p8267 = .success := by decide +kernel
theorem unsat8267 : Unsatisfiable (PosFin 65) f8267 := by
  apply lratCheckerSound f8267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8267
  · intro a ha; simp [p8267] at ha; subst a; trivial
  · exact checked8267
theorem derived8267 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8267 := by
  apply localUnsat_implies_entails f8267 [c2372, c2147, c2643] c8267 unsat8267 (by rfl) a
  have h0 : Entails.eval a c2372 := h 2371 (by decide)
  have h1 : Entails.eval a c2147 := h 2146 (by decide)
  have h2 : Entails.eval a c2643 := h 2642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8268 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8268 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2001, some c570, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8268 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8268 : lratChecker f8268 p8268 = .success := by decide +kernel
theorem unsat8268 : Unsatisfiable (PosFin 65) f8268 := by
  apply lratCheckerSound f8268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8268
  · intro a ha; simp [p8268] at ha; subst a; trivial
  · exact checked8268
theorem derived8268 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8268 := by
  apply localUnsat_implies_entails f8268 [c2001, c570] c8268 unsat8268 (by rfl) a
  have h0 : Entails.eval a c2001 := h 2000 (by decide)
  have h1 : Entails.eval a c570 := h 569 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8269 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8269 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8221, some c8159, some c7849, some c8244, some c8250, some c8264, some c8248, some c8249, some c8266, some c8267, some c8262, some c8268, some c8263, some c7926, some c2374, some c2384, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8269 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8269 : lratChecker f8269 p8269 = .success := by decide +kernel
theorem unsat8269 : Unsatisfiable (PosFin 65) f8269 := by
  apply lratCheckerSound f8269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8269
  · intro a ha; simp [p8269] at ha; subst a; trivial
  · exact checked8269
theorem derived8269 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8269 := by
  apply localUnsat_implies_entails f8269 [c8221, c8159, c7849, c8244, c8250, c8264, c8248, c8249, c8266, c8267, c8262, c8268, c8263, c7926, c2374, c2384] c8269 unsat8269 (by rfl) a
  have h0 : Entails.eval a c8221 := derived8221 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8244 := derived8244 a h
  have h4 : Entails.eval a c8250 := derived8250 a h
  have h5 : Entails.eval a c8264 := derived8264 a h
  have h6 : Entails.eval a c8248 := derived8248 a h
  have h7 : Entails.eval a c8249 := derived8249 a h
  have h8 : Entails.eval a c8266 := derived8266 a h
  have h9 : Entails.eval a c8267 := derived8267 a h
  have h10 : Entails.eval a c8262 := derived8262 a h
  have h11 : Entails.eval a c8268 := derived8268 a h
  have h12 : Entails.eval a c8263 := derived8263 a h
  have h13 : Entails.eval a c7926 := derived7926 a h
  have h14 : Entails.eval a c2374 := h 2373 (by decide)
  have h15 : Entails.eval a c2384 := h 2383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8270 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8270 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c545, some c553, some c8036, some c682, some c544, some c8208, some c2573, some c7926, some c513, some c1332, some c603, some c2632, some c1049, some c7794, some c2654, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8270 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8270 : lratChecker f8270 p8270 = .success := by decide +kernel
theorem unsat8270 : Unsatisfiable (PosFin 65) f8270 := by
  apply lratCheckerSound f8270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8270
  · intro a ha; simp [p8270] at ha; subst a; trivial
  · exact checked8270
theorem derived8270 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8270 := by
  apply localUnsat_implies_entails f8270 [c545, c553, c8036, c682, c544, c8208, c2573, c7926, c513, c1332, c603, c2632, c1049, c7794, c2654] c8270 unsat8270 (by rfl) a
  have h0 : Entails.eval a c545 := h 544 (by decide)
  have h1 : Entails.eval a c553 := h 552 (by decide)
  have h2 : Entails.eval a c8036 := derived8036 a h
  have h3 : Entails.eval a c682 := h 681 (by decide)
  have h4 : Entails.eval a c544 := h 543 (by decide)
  have h5 : Entails.eval a c8208 := derived8208 a h
  have h6 : Entails.eval a c2573 := h 2572 (by decide)
  have h7 : Entails.eval a c7926 := derived7926 a h
  have h8 : Entails.eval a c513 := h 512 (by decide)
  have h9 : Entails.eval a c1332 := h 1331 (by decide)
  have h10 : Entails.eval a c603 := h 602 (by decide)
  have h11 : Entails.eval a c2632 := h 2631 (by decide)
  have h12 : Entails.eval a c1049 := h 1048 (by decide)
  have h13 : Entails.eval a c7794 := derived7794 a h
  have h14 : Entails.eval a c2654 := h 2653 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8271 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8271 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8208, some c8242, some c907, some c931, some c881, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8271 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8271 : lratChecker f8271 p8271 = .success := by decide +kernel
theorem unsat8271 : Unsatisfiable (PosFin 65) f8271 := by
  apply lratCheckerSound f8271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8271
  · intro a ha; simp [p8271] at ha; subst a; trivial
  · exact checked8271
theorem derived8271 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8271 := by
  apply localUnsat_implies_entails f8271 [c8208, c8242, c907, c931, c881] c8271 unsat8271 (by rfl) a
  have h0 : Entails.eval a c8208 := derived8208 a h
  have h1 : Entails.eval a c8242 := derived8242 a h
  have h2 : Entails.eval a c907 := h 906 (by decide)
  have h3 : Entails.eval a c931 := h 930 (by decide)
  have h4 : Entails.eval a c881 := h 880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8272 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8272 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1309, some c907, some c1332, some c1097, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p8272 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8272 : lratChecker f8272 p8272 = .success := by decide +kernel
theorem unsat8272 : Unsatisfiable (PosFin 65) f8272 := by
  apply lratCheckerSound f8272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8272
  · intro a ha; simp [p8272] at ha; subst a; trivial
  · exact checked8272
theorem derived8272 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8272 := by
  apply localUnsat_implies_entails f8272 [c1309, c907, c1332, c1097] c8272 unsat8272 (by rfl) a
  have h0 : Entails.eval a c1309 := h 1308 (by decide)
  have h1 : Entails.eval a c907 := h 906 (by decide)
  have h2 : Entails.eval a c1332 := h 1331 (by decide)
  have h3 : Entails.eval a c1097 := h 1096 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8273 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8273 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7941, some c8269, some c8221, some c8159, some c7849, some c8270, some c8240, some c8175, some c8208, some c8271, some c8030, some c8272, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8273 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8273 : lratChecker f8273 p8273 = .success := by decide +kernel
theorem unsat8273 : Unsatisfiable (PosFin 65) f8273 := by
  apply lratCheckerSound f8273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8273
  · intro a ha; simp [p8273] at ha; subst a; trivial
  · exact checked8273
theorem derived8273 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8273 := by
  apply localUnsat_implies_entails f8273 [c7941, c8269, c8221, c8159, c7849, c8270, c8240, c8175, c8208, c8271, c8030, c8272] c8273 unsat8273 (by rfl) a
  have h0 : Entails.eval a c7941 := derived7941 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8221 := derived8221 a h
  have h3 : Entails.eval a c8159 := derived8159 a h
  have h4 : Entails.eval a c7849 := derived7849 a h
  have h5 : Entails.eval a c8270 := derived8270 a h
  have h6 : Entails.eval a c8240 := derived8240 a h
  have h7 : Entails.eval a c8175 := derived8175 a h
  have h8 : Entails.eval a c8208 := derived8208 a h
  have h9 : Entails.eval a c8271 := derived8271 a h
  have h10 : Entails.eval a c8030 := derived8030 a h
  have h11 : Entails.eval a c8272 := derived8272 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8274 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8274 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8227, some c8231, some c2399, some c2404, some c682, some c2259, some c1858, some c2247, some c2262, some c1599, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8274 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8274 : lratChecker f8274 p8274 = .success := by decide +kernel
theorem unsat8274 : Unsatisfiable (PosFin 65) f8274 := by
  apply lratCheckerSound f8274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8274
  · intro a ha; simp [p8274] at ha; subst a; trivial
  · exact checked8274
theorem derived8274 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8274 := by
  apply localUnsat_implies_entails f8274 [c8227, c8231, c2399, c2404, c682, c2259, c1858, c2247, c2262, c1599] c8274 unsat8274 (by rfl) a
  have h0 : Entails.eval a c8227 := derived8227 a h
  have h1 : Entails.eval a c8231 := derived8231 a h
  have h2 : Entails.eval a c2399 := h 2398 (by decide)
  have h3 : Entails.eval a c2404 := h 2403 (by decide)
  have h4 : Entails.eval a c682 := h 681 (by decide)
  have h5 : Entails.eval a c2259 := h 2258 (by decide)
  have h6 : Entails.eval a c1858 := h 1857 (by decide)
  have h7 : Entails.eval a c2247 := h 2246 (by decide)
  have h8 : Entails.eval a c2262 := h 2261 (by decide)
  have h9 : Entails.eval a c1599 := h 1598 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8275 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8275 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8239, some c2247, some c2517, some c145, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8275 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8275 : lratChecker f8275 p8275 = .success := by decide +kernel
theorem unsat8275 : Unsatisfiable (PosFin 65) f8275 := by
  apply lratCheckerSound f8275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8275
  · intro a ha; simp [p8275] at ha; subst a; trivial
  · exact checked8275
theorem derived8275 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8275 := by
  apply localUnsat_implies_entails f8275 [c8239, c2247, c2517, c145] c8275 unsat8275 (by rfl) a
  have h0 : Entails.eval a c8239 := derived8239 a h
  have h1 : Entails.eval a c2247 := h 2246 (by decide)
  have h2 : Entails.eval a c2517 := h 2516 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8276 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨28, by decide⟩, true), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8276 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c827, some c835, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8276 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8276 : lratChecker f8276 p8276 = .success := by decide +kernel
theorem unsat8276 : Unsatisfiable (PosFin 65) f8276 := by
  apply lratCheckerSound f8276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8276
  · intro a ha; simp [p8276] at ha; subst a; trivial
  · exact checked8276
theorem derived8276 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8276 := by
  apply localUnsat_implies_entails f8276 [c827, c835] c8276 unsat8276 (by rfl) a
  have h0 : Entails.eval a c827 := h 826 (by decide)
  have h1 : Entails.eval a c835 := h 834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8277 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8277 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c688, some c683, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8277 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8277 : lratChecker f8277 p8277 = .success := by decide +kernel
theorem unsat8277 : Unsatisfiable (PosFin 65) f8277 := by
  apply lratCheckerSound f8277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8277
  · intro a ha; simp [p8277] at ha; subst a; trivial
  · exact checked8277
theorem derived8277 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8277 := by
  apply localUnsat_implies_entails f8277 [c688, c683] c8277 unsat8277 (by rfl) a
  have h0 : Entails.eval a c688 := h 687 (by decide)
  have h1 : Entails.eval a c683 := h 682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8278 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8278 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8274, some c8275, some c8277, some c2244, some c1936, some c2034, some c2051, some c2633, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8278 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8278 : lratChecker f8278 p8278 = .success := by decide +kernel
theorem unsat8278 : Unsatisfiable (PosFin 65) f8278 := by
  apply lratCheckerSound f8278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8278
  · intro a ha; simp [p8278] at ha; subst a; trivial
  · exact checked8278
theorem derived8278 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8278 := by
  apply localUnsat_implies_entails f8278 [c8274, c8275, c8277, c2244, c1936, c2034, c2051, c2633] c8278 unsat8278 (by rfl) a
  have h0 : Entails.eval a c8274 := derived8274 a h
  have h1 : Entails.eval a c8275 := derived8275 a h
  have h2 : Entails.eval a c8277 := derived8277 a h
  have h3 : Entails.eval a c2244 := h 2243 (by decide)
  have h4 : Entails.eval a c1936 := h 1935 (by decide)
  have h5 : Entails.eval a c2034 := h 2033 (by decide)
  have h6 : Entails.eval a c2051 := h 2050 (by decide)
  have h7 : Entails.eval a c2633 := h 2632 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8279 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8279 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8231, some c8242, some c2399, some c2404, some c7592, some c885, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8279 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8279 : lratChecker f8279 p8279 = .success := by decide +kernel
theorem unsat8279 : Unsatisfiable (PosFin 65) f8279 := by
  apply lratCheckerSound f8279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8279
  · intro a ha; simp [p8279] at ha; subst a; trivial
  · exact checked8279
theorem derived8279 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8279 := by
  apply localUnsat_implies_entails f8279 [c8231, c8242, c2399, c2404, c7592, c885] c8279 unsat8279 (by rfl) a
  have h0 : Entails.eval a c8231 := derived8231 a h
  have h1 : Entails.eval a c8242 := derived8242 a h
  have h2 : Entails.eval a c2399 := h 2398 (by decide)
  have h3 : Entails.eval a c2404 := h 2403 (by decide)
  have h4 : Entails.eval a c7592 := derived7592 a h
  have h5 : Entails.eval a c885 := h 884 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8280 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8280 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8221, some c8159, some c7849, some c7941, some c8273, some c8278, some c8240, some c8175, some c8201, some c8279, some c8030, some c1936, some c1897, some c577, some c582, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8280 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8280 : lratChecker f8280 p8280 = .success := by decide +kernel
theorem unsat8280 : Unsatisfiable (PosFin 65) f8280 := by
  apply lratCheckerSound f8280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8280
  · intro a ha; simp [p8280] at ha; subst a; trivial
  · exact checked8280
theorem derived8280 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8280 := by
  apply localUnsat_implies_entails f8280 [c8269, c8221, c8159, c7849, c7941, c8273, c8278, c8240, c8175, c8201, c8279, c8030, c1936, c1897, c577, c582] c8280 unsat8280 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8221 := derived8221 a h
  have h2 : Entails.eval a c8159 := derived8159 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c7941 := derived7941 a h
  have h5 : Entails.eval a c8273 := derived8273 a h
  have h6 : Entails.eval a c8278 := derived8278 a h
  have h7 : Entails.eval a c8240 := derived8240 a h
  have h8 : Entails.eval a c8175 := derived8175 a h
  have h9 : Entails.eval a c8201 := derived8201 a h
  have h10 : Entails.eval a c8279 := derived8279 a h
  have h11 : Entails.eval a c8030 := derived8030 a h
  have h12 : Entails.eval a c1936 := h 1935 (by decide)
  have h13 : Entails.eval a c1897 := h 1896 (by decide)
  have h14 : Entails.eval a c577 := h 576 (by decide)
  have h15 : Entails.eval a c582 := h 581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8280

end CochromaticTwenty.Certificates.FixedCore1
