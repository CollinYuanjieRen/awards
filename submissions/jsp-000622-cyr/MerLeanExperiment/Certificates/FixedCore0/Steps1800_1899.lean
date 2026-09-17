import MerLeanExperiment.Certificates.FixedCore0.Steps1700_1799

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9351 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9351 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9129, some c9350, some c8420, some c4902, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9351 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9351 : lratChecker f9351 p9351 = .success := by decide +kernel
theorem unsat9351 : Unsatisfiable (PosFin 65) f9351 := by
  apply lratCheckerSound f9351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9351
  · intro a ha; simp [p9351] at ha; subst a; trivial
  · exact checked9351
theorem derived9351 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9351 := by
  apply localUnsat_implies_entails f9351 [c9347, c9129, c9350, c8420, c4902] c9351 unsat9351 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9129 := derived9129 a h
  have h2 : Entails.eval a c9350 := derived9350 a h
  have h3 : Entails.eval a c8420 := derived8420 a h
  have h4 : Entails.eval a c4902 := h 4901 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9352 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9352 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4546, some c9348, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9352 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9352 : lratChecker f9352 p9352 = .success := by decide +kernel
theorem unsat9352 : Unsatisfiable (PosFin 65) f9352 := by
  apply lratCheckerSound f9352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9352
  · intro a ha; simp [p9352] at ha; subst a; trivial
  · exact checked9352
theorem derived9352 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9352 := by
  apply localUnsat_implies_entails f9352 [c4546, c9348] c9352 unsat9352 (by rfl) a
  have h0 : Entails.eval a c4546 := h 4545 (by decide)
  have h1 : Entails.eval a c9348 := derived9348 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9353 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9353 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c1443, some c4639, some c3166, some c2889, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9353 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9353 : lratChecker f9353 p9353 = .success := by decide +kernel
theorem unsat9353 : Unsatisfiable (PosFin 65) f9353 := by
  apply lratCheckerSound f9353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9353
  · intro a ha; simp [p9353] at ha; subst a; trivial
  · exact checked9353
theorem derived9353 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9353 := by
  apply localUnsat_implies_entails f9353 [c9347, c1443, c4639, c3166, c2889] c9353 unsat9353 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c1443 := h 1442 (by decide)
  have h2 : Entails.eval a c4639 := h 4638 (by decide)
  have h3 : Entails.eval a c3166 := h 3165 (by decide)
  have h4 : Entails.eval a c2889 := h 2888 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9354 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9354 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9353, some c9351, some c9352, some c8420, some c8930, some c8689, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9354 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9354 : lratChecker f9354 p9354 = .success := by decide +kernel
theorem unsat9354 : Unsatisfiable (PosFin 65) f9354 := by
  apply lratCheckerSound f9354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9354
  · intro a ha; simp [p9354] at ha; subst a; trivial
  · exact checked9354
theorem derived9354 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9354 := by
  apply localUnsat_implies_entails f9354 [c9353, c9351, c9352, c8420, c8930, c8689] c9354 unsat9354 (by rfl) a
  have h0 : Entails.eval a c9353 := derived9353 a h
  have h1 : Entails.eval a c9351 := derived9351 a h
  have h2 : Entails.eval a c9352 := derived9352 a h
  have h3 : Entails.eval a c8420 := derived8420 a h
  have h4 : Entails.eval a c8930 := derived8930 a h
  have h5 : Entails.eval a c8689 := derived8689 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9355 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨13, by decide⟩, true), (⟨58, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9355 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4611, some c2910, some c3146, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9355 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9355 : lratChecker f9355 p9355 = .success := by decide +kernel
theorem unsat9355 : Unsatisfiable (PosFin 65) f9355 := by
  apply lratCheckerSound f9355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9355
  · intro a ha; simp [p9355] at ha; subst a; trivial
  · exact checked9355
theorem derived9355 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9355 := by
  apply localUnsat_implies_entails f9355 [c4611, c2910, c3146] c9355 unsat9355 (by rfl) a
  have h0 : Entails.eval a c4611 := h 4610 (by decide)
  have h1 : Entails.eval a c2910 := h 2909 (by decide)
  have h2 : Entails.eval a c3146 := h 3145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9356 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9356 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2852, some c2853, some c2872, some c2851, some c2850, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9356 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9356 : lratChecker f9356 p9356 = .success := by decide +kernel
theorem unsat9356 : Unsatisfiable (PosFin 65) f9356 := by
  apply lratCheckerSound f9356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9356
  · intro a ha; simp [p9356] at ha; subst a; trivial
  · exact checked9356
theorem derived9356 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9356 := by
  apply localUnsat_implies_entails f9356 [c2852, c2853, c2872, c2851, c2850] c9356 unsat9356 (by rfl) a
  have h0 : Entails.eval a c2852 := h 2851 (by decide)
  have h1 : Entails.eval a c2853 := h 2852 (by decide)
  have h2 : Entails.eval a c2872 := h 2871 (by decide)
  have h3 : Entails.eval a c2851 := h 2850 (by decide)
  have h4 : Entails.eval a c2850 := h 2849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9357 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9357 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9353, some c9354, some c9213, some c9355, some c8420, some c9356, some c9129, some c8930, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9357 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9357 : lratChecker f9357 p9357 = .success := by decide +kernel
theorem unsat9357 : Unsatisfiable (PosFin 65) f9357 := by
  apply lratCheckerSound f9357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9357
  · intro a ha; simp [p9357] at ha; subst a; trivial
  · exact checked9357
theorem derived9357 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9357 := by
  apply localUnsat_implies_entails f9357 [c9347, c9353, c9354, c9213, c9355, c8420, c9356, c9129, c8930] c9357 unsat9357 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9353 := derived9353 a h
  have h2 : Entails.eval a c9354 := derived9354 a h
  have h3 : Entails.eval a c9213 := derived9213 a h
  have h4 : Entails.eval a c9355 := derived9355 a h
  have h5 : Entails.eval a c8420 := derived8420 a h
  have h6 : Entails.eval a c9356 := derived9356 a h
  have h7 : Entails.eval a c9129 := derived9129 a h
  have h8 : Entails.eval a c8930 := derived8930 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9358 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9358 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4619, some c4858, some c3195, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9358 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9358 : lratChecker f9358 p9358 = .success := by decide +kernel
theorem unsat9358 : Unsatisfiable (PosFin 65) f9358 := by
  apply lratCheckerSound f9358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9358
  · intro a ha; simp [p9358] at ha; subst a; trivial
  · exact checked9358
theorem derived9358 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9358 := by
  apply localUnsat_implies_entails f9358 [c4619, c4858, c3195] c9358 unsat9358 (by rfl) a
  have h0 : Entails.eval a c4619 := h 4618 (by decide)
  have h1 : Entails.eval a c4858 := h 4857 (by decide)
  have h2 : Entails.eval a c3195 := h 3194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9359 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9359 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4574, some c3160, some c2885, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9359 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9359 : lratChecker f9359 p9359 = .success := by decide +kernel
theorem unsat9359 : Unsatisfiable (PosFin 65) f9359 := by
  apply lratCheckerSound f9359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9359
  · intro a ha; simp [p9359] at ha; subst a; trivial
  · exact checked9359
theorem derived9359 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9359 := by
  apply localUnsat_implies_entails f9359 [c4574, c3160, c2885] c9359 unsat9359 (by rfl) a
  have h0 : Entails.eval a c4574 := h 4573 (by decide)
  have h1 : Entails.eval a c3160 := h 3159 (by decide)
  have h2 : Entails.eval a c2885 := h 2884 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9360 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9360 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9357, some c3740, some c9352, some c9358, some c9154, some c8689, some c9359, some c3726, some c3734, some c9115, some c9264, some c9166, some c3701, some c3702, some c723, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9360 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9360 : lratChecker f9360 p9360 = .success := by decide +kernel
theorem unsat9360 : Unsatisfiable (PosFin 65) f9360 := by
  apply lratCheckerSound f9360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9360
  · intro a ha; simp [p9360] at ha; subst a; trivial
  · exact checked9360
theorem derived9360 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9360 := by
  apply localUnsat_implies_entails f9360 [c9347, c9357, c3740, c9352, c9358, c9154, c8689, c9359, c3726, c3734, c9115, c9264, c9166, c3701, c3702, c723] c9360 unsat9360 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9357 := derived9357 a h
  have h2 : Entails.eval a c3740 := h 3739 (by decide)
  have h3 : Entails.eval a c9352 := derived9352 a h
  have h4 : Entails.eval a c9358 := derived9358 a h
  have h5 : Entails.eval a c9154 := derived9154 a h
  have h6 : Entails.eval a c8689 := derived8689 a h
  have h7 : Entails.eval a c9359 := derived9359 a h
  have h8 : Entails.eval a c3726 := h 3725 (by decide)
  have h9 : Entails.eval a c3734 := h 3733 (by decide)
  have h10 : Entails.eval a c9115 := derived9115 a h
  have h11 : Entails.eval a c9264 := derived9264 a h
  have h12 : Entails.eval a c9166 := derived9166 a h
  have h13 : Entails.eval a c3701 := h 3700 (by decide)
  have h14 : Entails.eval a c3702 := h 3701 (by decide)
  have h15 : Entails.eval a c723 := h 722 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9361 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9361 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1418, some c1239, some c1428, some c1439, some c1218, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9361 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9361 : lratChecker f9361 p9361 = .success := by decide +kernel
theorem unsat9361 : Unsatisfiable (PosFin 65) f9361 := by
  apply lratCheckerSound f9361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9361
  · intro a ha; simp [p9361] at ha; subst a; trivial
  · exact checked9361
theorem derived9361 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9361 := by
  apply localUnsat_implies_entails f9361 [c1418, c1239, c1428, c1439, c1218] c9361 unsat9361 (by rfl) a
  have h0 : Entails.eval a c1418 := h 1417 (by decide)
  have h1 : Entails.eval a c1239 := h 1238 (by decide)
  have h2 : Entails.eval a c1428 := h 1427 (by decide)
  have h3 : Entails.eval a c1439 := h 1438 (by decide)
  have h4 : Entails.eval a c1218 := h 1217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9362 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9362 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9110, some c2682, some c4345, some c4861, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9362 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9362 : lratChecker f9362 p9362 = .success := by decide +kernel
theorem unsat9362 : Unsatisfiable (PosFin 65) f9362 := by
  apply lratCheckerSound f9362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9362
  · intro a ha; simp [p9362] at ha; subst a; trivial
  · exact checked9362
theorem derived9362 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9362 := by
  apply localUnsat_implies_entails f9362 [c9110, c2682, c4345, c4861] c9362 unsat9362 (by rfl) a
  have h0 : Entails.eval a c9110 := derived9110 a h
  have h1 : Entails.eval a c2682 := h 2681 (by decide)
  have h2 : Entails.eval a c4345 := h 4344 (by decide)
  have h3 : Entails.eval a c4861 := h 4860 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9363 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9363 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4573, some c4612, some c4625, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9363 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9363 : lratChecker f9363 p9363 = .success := by decide +kernel
theorem unsat9363 : Unsatisfiable (PosFin 65) f9363 := by
  apply lratCheckerSound f9363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9363
  · intro a ha; simp [p9363] at ha; subst a; trivial
  · exact checked9363
theorem derived9363 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9363 := by
  apply localUnsat_implies_entails f9363 [c4573, c4612, c4625] c9363 unsat9363 (by rfl) a
  have h0 : Entails.eval a c4573 := h 4572 (by decide)
  have h1 : Entails.eval a c4612 := h 4611 (by decide)
  have h2 : Entails.eval a c4625 := h 4624 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9364 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨7, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9364 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4375, some c4860, some c4342, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9364 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9364 : lratChecker f9364 p9364 = .success := by decide +kernel
theorem unsat9364 : Unsatisfiable (PosFin 65) f9364 := by
  apply lratCheckerSound f9364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9364
  · intro a ha; simp [p9364] at ha; subst a; trivial
  · exact checked9364
theorem derived9364 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9364 := by
  apply localUnsat_implies_entails f9364 [c4375, c4860, c4342] c9364 unsat9364 (by rfl) a
  have h0 : Entails.eval a c4375 := h 4374 (by decide)
  have h1 : Entails.eval a c4860 := h 4859 (by decide)
  have h2 : Entails.eval a c4342 := h 4341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9365 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9365 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9352, some c9362, some c9363, some c9364, some c8000, some c3191, some c4855, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9365 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9365 : lratChecker f9365 p9365 = .success := by decide +kernel
theorem unsat9365 : Unsatisfiable (PosFin 65) f9365 := by
  apply lratCheckerSound f9365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9365
  · intro a ha; simp [p9365] at ha; subst a; trivial
  · exact checked9365
theorem derived9365 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9365 := by
  apply localUnsat_implies_entails f9365 [c9352, c9362, c9363, c9364, c8000, c3191, c4855] c9365 unsat9365 (by rfl) a
  have h0 : Entails.eval a c9352 := derived9352 a h
  have h1 : Entails.eval a c9362 := derived9362 a h
  have h2 : Entails.eval a c9363 := derived9363 a h
  have h3 : Entails.eval a c9364 := derived9364 a h
  have h4 : Entails.eval a c8000 := derived8000 a h
  have h5 : Entails.eval a c3191 := h 3190 (by decide)
  have h6 : Entails.eval a c4855 := h 4854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9366 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9366 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9352, some c9360, some c9347, some c9365, some c1418, some c1428, some c8000, some c1218, some c4612, some c4855, some c3204, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9366 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9366 : lratChecker f9366 p9366 = .success := by decide +kernel
theorem unsat9366 : Unsatisfiable (PosFin 65) f9366 := by
  apply lratCheckerSound f9366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9366
  · intro a ha; simp [p9366] at ha; subst a; trivial
  · exact checked9366
theorem derived9366 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9366 := by
  apply localUnsat_implies_entails f9366 [c9352, c9360, c9347, c9365, c1418, c1428, c8000, c1218, c4612, c4855, c3204] c9366 unsat9366 (by rfl) a
  have h0 : Entails.eval a c9352 := derived9352 a h
  have h1 : Entails.eval a c9360 := derived9360 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9365 := derived9365 a h
  have h4 : Entails.eval a c1418 := h 1417 (by decide)
  have h5 : Entails.eval a c1428 := h 1427 (by decide)
  have h6 : Entails.eval a c8000 := derived8000 a h
  have h7 : Entails.eval a c1218 := h 1217 (by decide)
  have h8 : Entails.eval a c4612 := h 4611 (by decide)
  have h9 : Entails.eval a c4855 := h 4854 (by decide)
  have h10 : Entails.eval a c3204 := h 3203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9367 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9367 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1433, some c9115, some c9195, some c8496, some c8580, some c1398, some c1399, some c1403, some c708, some c709, some c683, some c685, some c1416, some c1402, some c1209, some c5454, some c1206, some c5458, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9367 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9367 : lratChecker f9367 p9367 = .success := by decide +kernel
theorem unsat9367 : Unsatisfiable (PosFin 65) f9367 := by
  apply lratCheckerSound f9367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9367
  · intro a ha; simp [p9367] at ha; subst a; trivial
  · exact checked9367
theorem derived9367 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9367 := by
  apply localUnsat_implies_entails f9367 [c1433, c9115, c9195, c8496, c8580, c1398, c1399, c1403, c708, c709, c683, c685, c1416, c1402, c1209, c5454, c1206, c5458] c9367 unsat9367 (by rfl) a
  have h0 : Entails.eval a c1433 := h 1432 (by decide)
  have h1 : Entails.eval a c9115 := derived9115 a h
  have h2 : Entails.eval a c9195 := derived9195 a h
  have h3 : Entails.eval a c8496 := derived8496 a h
  have h4 : Entails.eval a c8580 := derived8580 a h
  have h5 : Entails.eval a c1398 := h 1397 (by decide)
  have h6 : Entails.eval a c1399 := h 1398 (by decide)
  have h7 : Entails.eval a c1403 := h 1402 (by decide)
  have h8 : Entails.eval a c708 := h 707 (by decide)
  have h9 : Entails.eval a c709 := h 708 (by decide)
  have h10 : Entails.eval a c683 := h 682 (by decide)
  have h11 : Entails.eval a c685 := h 684 (by decide)
  have h12 : Entails.eval a c1416 := h 1415 (by decide)
  have h13 : Entails.eval a c1402 := h 1401 (by decide)
  have h14 : Entails.eval a c1209 := h 1208 (by decide)
  have h15 : Entails.eval a c5454 := h 5453 (by decide)
  have h16 : Entails.eval a c1206 := h 1205 (by decide)
  have h17 : Entails.eval a c5458 := h 5457 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9368 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨58, by decide⟩, true), (⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9368 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2682, some c4463, some c4345, some c4861, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9368 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9368 : lratChecker f9368 p9368 = .success := by decide +kernel
theorem unsat9368 : Unsatisfiable (PosFin 65) f9368 := by
  apply lratCheckerSound f9368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9368
  · intro a ha; simp [p9368] at ha; subst a; trivial
  · exact checked9368
theorem derived9368 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9368 := by
  apply localUnsat_implies_entails f9368 [c2682, c4463, c4345, c4861] c9368 unsat9368 (by rfl) a
  have h0 : Entails.eval a c2682 := h 2681 (by decide)
  have h1 : Entails.eval a c4463 := h 4462 (by decide)
  have h2 : Entails.eval a c4345 := h 4344 (by decide)
  have h3 : Entails.eval a c4861 := h 4860 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9369 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9369 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2666, some c4696, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9369 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9369 : lratChecker f9369 p9369 = .success := by decide +kernel
theorem unsat9369 : Unsatisfiable (PosFin 65) f9369 := by
  apply lratCheckerSound f9369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9369
  · intro a ha; simp [p9369] at ha; subst a; trivial
  · exact checked9369
theorem derived9369 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9369 := by
  apply localUnsat_implies_entails f9369 [c2666, c4696] c9369 unsat9369 (by rfl) a
  have h0 : Entails.eval a c2666 := h 2665 (by decide)
  have h1 : Entails.eval a c4696 := h 4695 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9370 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9370 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4847, some c4844, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9370 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9370 : lratChecker f9370 p9370 = .success := by decide +kernel
theorem unsat9370 : Unsatisfiable (PosFin 65) f9370 := by
  apply lratCheckerSound f9370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9370
  · intro a ha; simp [p9370] at ha; subst a; trivial
  · exact checked9370
theorem derived9370 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9370 := by
  apply localUnsat_implies_entails f9370 [c4847, c4844] c9370 unsat9370 (by rfl) a
  have h0 : Entails.eval a c4847 := h 4846 (by decide)
  have h1 : Entails.eval a c4844 := h 4843 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9371 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9371 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9360, some c9347, some c9352, some c9366, some c9367, some c9368, some c9115, some c9195, some c8496, some c8580, some c9369, some c9370, some c3180, some c3175, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9371 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9371 : lratChecker f9371 p9371 = .success := by decide +kernel
theorem unsat9371 : Unsatisfiable (PosFin 65) f9371 := by
  apply lratCheckerSound f9371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9371
  · intro a ha; simp [p9371] at ha; subst a; trivial
  · exact checked9371
theorem derived9371 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9371 := by
  apply localUnsat_implies_entails f9371 [c9360, c9347, c9352, c9366, c9367, c9368, c9115, c9195, c8496, c8580, c9369, c9370, c3180, c3175] c9371 unsat9371 (by rfl) a
  have h0 : Entails.eval a c9360 := derived9360 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9352 := derived9352 a h
  have h3 : Entails.eval a c9366 := derived9366 a h
  have h4 : Entails.eval a c9367 := derived9367 a h
  have h5 : Entails.eval a c9368 := derived9368 a h
  have h6 : Entails.eval a c9115 := derived9115 a h
  have h7 : Entails.eval a c9195 := derived9195 a h
  have h8 : Entails.eval a c8496 := derived8496 a h
  have h9 : Entails.eval a c8580 := derived8580 a h
  have h10 : Entails.eval a c9369 := derived9369 a h
  have h11 : Entails.eval a c9370 := derived9370 a h
  have h12 : Entails.eval a c3180 := h 3179 (by decide)
  have h13 : Entails.eval a c3175 := h 3174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9372 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9372 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1211, some c1241, some c1240, some c1225, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9372 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9372 : lratChecker f9372 p9372 = .success := by decide +kernel
theorem unsat9372 : Unsatisfiable (PosFin 65) f9372 := by
  apply lratCheckerSound f9372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9372
  · intro a ha; simp [p9372] at ha; subst a; trivial
  · exact checked9372
theorem derived9372 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9372 := by
  apply localUnsat_implies_entails f9372 [c1211, c1241, c1240, c1225] c9372 unsat9372 (by rfl) a
  have h0 : Entails.eval a c1211 := h 1210 (by decide)
  have h1 : Entails.eval a c1241 := h 1240 (by decide)
  have h2 : Entails.eval a c1240 := h 1239 (by decide)
  have h3 : Entails.eval a c1225 := h 1224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9373 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9373 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4901, some c4903, some c4909, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p9373 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9373 : lratChecker f9373 p9373 = .success := by decide +kernel
theorem unsat9373 : Unsatisfiable (PosFin 65) f9373 := by
  apply lratCheckerSound f9373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9373
  · intro a ha; simp [p9373] at ha; subst a; trivial
  · exact checked9373
theorem derived9373 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9373 := by
  apply localUnsat_implies_entails f9373 [c4901, c4903, c4909] c9373 unsat9373 (by rfl) a
  have h0 : Entails.eval a c4901 := h 4900 (by decide)
  have h1 : Entails.eval a c4903 := h 4902 (by decide)
  have h2 : Entails.eval a c4909 := h 4908 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9374 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9374 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8420, some c9373, some c1211, some c8780, some c9372, some c1428, some c1432, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9374 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9374 : lratChecker f9374 p9374 = .success := by decide +kernel
theorem unsat9374 : Unsatisfiable (PosFin 65) f9374 := by
  apply lratCheckerSound f9374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9374
  · intro a ha; simp [p9374] at ha; subst a; trivial
  · exact checked9374
theorem derived9374 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9374 := by
  apply localUnsat_implies_entails f9374 [c8420, c9373, c1211, c8780, c9372, c1428, c1432] c9374 unsat9374 (by rfl) a
  have h0 : Entails.eval a c8420 := derived8420 a h
  have h1 : Entails.eval a c9373 := derived9373 a h
  have h2 : Entails.eval a c1211 := h 1210 (by decide)
  have h3 : Entails.eval a c8780 := derived8780 a h
  have h4 : Entails.eval a c9372 := derived9372 a h
  have h5 : Entails.eval a c1428 := h 1427 (by decide)
  have h6 : Entails.eval a c1432 := h 1431 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9375 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9375 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9360, some c9371, some c8420, some c9374, some c9061, some c4892, some c4893, some c4916, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9375 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9375 : lratChecker f9375 p9375 = .success := by decide +kernel
theorem unsat9375 : Unsatisfiable (PosFin 65) f9375 := by
  apply lratCheckerSound f9375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9375
  · intro a ha; simp [p9375] at ha; subst a; trivial
  · exact checked9375
theorem derived9375 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9375 := by
  apply localUnsat_implies_entails f9375 [c9360, c9371, c8420, c9374, c9061, c4892, c4893, c4916] c9375 unsat9375 (by rfl) a
  have h0 : Entails.eval a c9360 := derived9360 a h
  have h1 : Entails.eval a c9371 := derived9371 a h
  have h2 : Entails.eval a c8420 := derived8420 a h
  have h3 : Entails.eval a c9374 := derived9374 a h
  have h4 : Entails.eval a c9061 := derived9061 a h
  have h5 : Entails.eval a c4892 := h 4891 (by decide)
  have h6 : Entails.eval a c4893 := h 4892 (by decide)
  have h7 : Entails.eval a c4916 := h 4915 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9376 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9376 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3703, some c3701, some c3702, some c3710, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p9376 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9376 : lratChecker f9376 p9376 = .success := by decide +kernel
theorem unsat9376 : Unsatisfiable (PosFin 65) f9376 := by
  apply lratCheckerSound f9376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9376
  · intro a ha; simp [p9376] at ha; subst a; trivial
  · exact checked9376
theorem derived9376 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9376 := by
  apply localUnsat_implies_entails f9376 [c3703, c3701, c3702, c3710] c9376 unsat9376 (by rfl) a
  have h0 : Entails.eval a c3703 := h 3702 (by decide)
  have h1 : Entails.eval a c3701 := h 3700 (by decide)
  have h2 : Entails.eval a c3702 := h 3701 (by decide)
  have h3 : Entails.eval a c3710 := h 3709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9377 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9377 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9264, some c9376, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9377 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9377 : lratChecker f9377 p9377 = .success := by decide +kernel
theorem unsat9377 : Unsatisfiable (PosFin 65) f9377 := by
  apply lratCheckerSound f9377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9377
  · intro a ha; simp [p9377] at ha; subst a; trivial
  · exact checked9377
theorem derived9377 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9377 := by
  apply localUnsat_implies_entails f9377 [c9264, c9376] c9377 unsat9377 (by rfl) a
  have h0 : Entails.eval a c9264 := derived9264 a h
  have h1 : Entails.eval a c9376 := derived9376 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9378 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨4, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9378 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3736, some c9146, some c9115, some c9377, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9378 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9378 : lratChecker f9378 p9378 = .success := by decide +kernel
theorem unsat9378 : Unsatisfiable (PosFin 65) f9378 := by
  apply lratCheckerSound f9378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9378
  · intro a ha; simp [p9378] at ha; subst a; trivial
  · exact checked9378
theorem derived9378 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9378 := by
  apply localUnsat_implies_entails f9378 [c3736, c9146, c9115, c9377] c9378 unsat9378 (by rfl) a
  have h0 : Entails.eval a c3736 := h 3735 (by decide)
  have h1 : Entails.eval a c9146 := derived9146 a h
  have h2 : Entails.eval a c9115 := derived9115 a h
  have h3 : Entails.eval a c9377 := derived9377 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9379 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9379 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4374, some c4724, some c4336, some c4857, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9379 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9379 : lratChecker f9379 p9379 = .success := by decide +kernel
theorem unsat9379 : Unsatisfiable (PosFin 65) f9379 := by
  apply lratCheckerSound f9379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9379
  · intro a ha; simp [p9379] at ha; subst a; trivial
  · exact checked9379
theorem derived9379 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9379 := by
  apply localUnsat_implies_entails f9379 [c4374, c4724, c4336, c4857] c9379 unsat9379 (by rfl) a
  have h0 : Entails.eval a c4374 := h 4373 (by decide)
  have h1 : Entails.eval a c4724 := h 4723 (by decide)
  have h2 : Entails.eval a c4336 := h 4335 (by decide)
  have h3 : Entails.eval a c4857 := h 4856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9380 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9380 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9375, some c9378, some c9352, some c9360, some c9372, some c9379, some c3718, some c3732, some c8007, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9380 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9380 : lratChecker f9380 p9380 = .success := by decide +kernel
theorem unsat9380 : Unsatisfiable (PosFin 65) f9380 := by
  apply lratCheckerSound f9380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9380
  · intro a ha; simp [p9380] at ha; subst a; trivial
  · exact checked9380
theorem derived9380 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9380 := by
  apply localUnsat_implies_entails f9380 [c9375, c9378, c9352, c9360, c9372, c9379, c3718, c3732, c8007] c9380 unsat9380 (by rfl) a
  have h0 : Entails.eval a c9375 := derived9375 a h
  have h1 : Entails.eval a c9378 := derived9378 a h
  have h2 : Entails.eval a c9352 := derived9352 a h
  have h3 : Entails.eval a c9360 := derived9360 a h
  have h4 : Entails.eval a c9372 := derived9372 a h
  have h5 : Entails.eval a c9379 := derived9379 a h
  have h6 : Entails.eval a c3718 := h 3717 (by decide)
  have h7 : Entails.eval a c3732 := h 3731 (by decide)
  have h8 : Entails.eval a c8007 := derived8007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9381 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9381 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9152, some c9035, some c1235, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9381 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9381 : lratChecker f9381 p9381 = .success := by decide +kernel
theorem unsat9381 : Unsatisfiable (PosFin 65) f9381 := by
  apply lratCheckerSound f9381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9381
  · intro a ha; simp [p9381] at ha; subst a; trivial
  · exact checked9381
theorem derived9381 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9381 := by
  apply localUnsat_implies_entails f9381 [c9152, c9035, c1235] c9381 unsat9381 (by rfl) a
  have h0 : Entails.eval a c9152 := derived9152 a h
  have h1 : Entails.eval a c9035 := derived9035 a h
  have h2 : Entails.eval a c1235 := h 1234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9382 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨4, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9382 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3734, some c3737, some c3738, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9382 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9382 : lratChecker f9382 p9382 = .success := by decide +kernel
theorem unsat9382 : Unsatisfiable (PosFin 65) f9382 := by
  apply lratCheckerSound f9382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9382
  · intro a ha; simp [p9382] at ha; subst a; trivial
  · exact checked9382
theorem derived9382 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9382 := by
  apply localUnsat_implies_entails f9382 [c3734, c3737, c3738] c9382 unsat9382 (by rfl) a
  have h0 : Entails.eval a c3734 := h 3733 (by decide)
  have h1 : Entails.eval a c3737 := h 3736 (by decide)
  have h2 : Entails.eval a c3738 := h 3737 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9383 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9383 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9360, some c9375, some c9380, some c9382, some c9115, some c9377, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9383 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9383 : lratChecker f9383 p9383 = .success := by decide +kernel
theorem unsat9383 : Unsatisfiable (PosFin 65) f9383 := by
  apply lratCheckerSound f9383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9383
  · intro a ha; simp [p9383] at ha; subst a; trivial
  · exact checked9383
theorem derived9383 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9383 := by
  apply localUnsat_implies_entails f9383 [c9360, c9375, c9380, c9382, c9115, c9377] c9383 unsat9383 (by rfl) a
  have h0 : Entails.eval a c9360 := derived9360 a h
  have h1 : Entails.eval a c9375 := derived9375 a h
  have h2 : Entails.eval a c9380 := derived9380 a h
  have h3 : Entails.eval a c9382 := derived9382 a h
  have h4 : Entails.eval a c9115 := derived9115 a h
  have h5 : Entails.eval a c9377 := derived9377 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9384 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨58, by decide⟩, true), (⟨4, by decide⟩, false), (⟨63, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9384 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c4555, some c1442, some c9349, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9384 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9384 : lratChecker f9384 p9384 = .success := by decide +kernel
theorem unsat9384 : Unsatisfiable (PosFin 65) f9384 := by
  apply lratCheckerSound f9384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9384
  · intro a ha; simp [p9384] at ha; subst a; trivial
  · exact checked9384
theorem derived9384 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9384 := by
  apply localUnsat_implies_entails f9384 [c9347, c4555, c1442, c9349] c9384 unsat9384 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c4555 := h 4554 (by decide)
  have h2 : Entails.eval a c1442 := h 1441 (by decide)
  have h3 : Entails.eval a c9349 := derived9349 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9385 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9385 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c1224, some c1239, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9385 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9385 : lratChecker f9385 p9385 = .success := by decide +kernel
theorem unsat9385 : Unsatisfiable (PosFin 65) f9385 := by
  apply lratCheckerSound f9385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9385
  · intro a ha; simp [p9385] at ha; subst a; trivial
  · exact checked9385
theorem derived9385 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9385 := by
  apply localUnsat_implies_entails f9385 [c7994, c1224, c1239] c9385 unsat9385 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c1224 := h 1223 (by decide)
  have h2 : Entails.eval a c1239 := h 1238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9386 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9386 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c2696, some c2685, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9386 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9386 : lratChecker f9386 p9386 = .success := by decide +kernel
theorem unsat9386 : Unsatisfiable (PosFin 65) f9386 := by
  apply lratCheckerSound f9386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9386
  · intro a ha; simp [p9386] at ha; subst a; trivial
  · exact checked9386
theorem derived9386 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9386 := by
  apply localUnsat_implies_entails f9386 [c7994, c2696, c2685] c9386 unsat9386 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c2696 := h 2695 (by decide)
  have h2 : Entails.eval a c2685 := h 2684 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9387 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9387 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8269, some c8435, some c8445, some c692, some c690, some c8580, some c705, some c684, some c655, some c8623, some c5845, some c289, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9387 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9387 : lratChecker f9387 p9387 = .success := by decide +kernel
theorem unsat9387 : Unsatisfiable (PosFin 65) f9387 := by
  apply lratCheckerSound f9387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9387
  · intro a ha; simp [p9387] at ha; subst a; trivial
  · exact checked9387
theorem derived9387 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9387 := by
  apply localUnsat_implies_entails f9387 [c8380, c8269, c8435, c8445, c692, c690, c8580, c705, c684, c655, c8623, c5845, c289] c9387 unsat9387 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8435 := derived8435 a h
  have h3 : Entails.eval a c8445 := derived8445 a h
  have h4 : Entails.eval a c692 := h 691 (by decide)
  have h5 : Entails.eval a c690 := h 689 (by decide)
  have h6 : Entails.eval a c8580 := derived8580 a h
  have h7 : Entails.eval a c705 := h 704 (by decide)
  have h8 : Entails.eval a c684 := h 683 (by decide)
  have h9 : Entails.eval a c655 := h 654 (by decide)
  have h10 : Entails.eval a c8623 := derived8623 a h
  have h11 : Entails.eval a c5845 := h 5844 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9388 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9388 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c9347, some c8300, some c8366, some c9352, some c9384, some c9385, some c9386, some c9387, some c9195, some c8496, some c8679, some c43, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9388 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9388 : lratChecker f9388 p9388 = .success := by decide +kernel
theorem unsat9388 : Unsatisfiable (PosFin 65) f9388 := by
  apply lratCheckerSound f9388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9388
  · intro a ha; simp [p9388] at ha; subst a; trivial
  · exact checked9388
theorem derived9388 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9388 := by
  apply localUnsat_implies_entails f9388 [c7994, c9347, c8300, c8366, c9352, c9384, c9385, c9386, c9387, c9195, c8496, c8679, c43] c9388 unsat9388 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c8300 := derived8300 a h
  have h3 : Entails.eval a c8366 := derived8366 a h
  have h4 : Entails.eval a c9352 := derived9352 a h
  have h5 : Entails.eval a c9384 := derived9384 a h
  have h6 : Entails.eval a c9385 := derived9385 a h
  have h7 : Entails.eval a c9386 := derived9386 a h
  have h8 : Entails.eval a c9387 := derived9387 a h
  have h9 : Entails.eval a c9195 := derived9195 a h
  have h10 : Entails.eval a c8496 := derived8496 a h
  have h11 : Entails.eval a c8679 := derived8679 a h
  have h12 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9389 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, true), (⟨1, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9389 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8930, some c9061, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p9389 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9389 : lratChecker f9389 p9389 = .success := by decide +kernel
theorem unsat9389 : Unsatisfiable (PosFin 65) f9389 := by
  apply lratCheckerSound f9389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9389
  · intro a ha; simp [p9389] at ha; subst a; trivial
  · exact checked9389
theorem derived9389 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9389 := by
  apply localUnsat_implies_entails f9389 [c8930, c9061] c9389 unsat9389 (by rfl) a
  have h0 : Entails.eval a c8930 := derived8930 a h
  have h1 : Entails.eval a c9061 := derived9061 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9390 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨64, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9390 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c9347, some c9388, some c8420, some c9389, some c4892, some c2858, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9390 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9390 : lratChecker f9390 p9390 = .success := by decide +kernel
theorem unsat9390 : Unsatisfiable (PosFin 65) f9390 := by
  apply lratCheckerSound f9390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9390
  · intro a ha; simp [p9390] at ha; subst a; trivial
  · exact checked9390
theorem derived9390 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9390 := by
  apply localUnsat_implies_entails f9390 [c8269, c7994, c9347, c9388, c8420, c9389, c4892, c2858] c9390 unsat9390 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9388 := derived9388 a h
  have h4 : Entails.eval a c8420 := derived8420 a h
  have h5 : Entails.eval a c9389 := derived9389 a h
  have h6 : Entails.eval a c4892 := h 4891 (by decide)
  have h7 : Entails.eval a c2858 := h 2857 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9391 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9391 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2677, some c4572, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9391 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9391 : lratChecker f9391 p9391 = .success := by decide +kernel
theorem unsat9391 : Unsatisfiable (PosFin 65) f9391 := by
  apply lratCheckerSound f9391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9391
  · intro a ha; simp [p9391] at ha; subst a; trivial
  · exact checked9391
theorem derived9391 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9391 := by
  apply localUnsat_implies_entails f9391 [c2677, c4572] c9391 unsat9391 (by rfl) a
  have h0 : Entails.eval a c2677 := h 2676 (by decide)
  have h1 : Entails.eval a c4572 := h 4571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9392 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨7, by decide⟩, false), (⟨59, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9392 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2547, some c3144, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9392 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9392 : lratChecker f9392 p9392 = .success := by decide +kernel
theorem unsat9392 : Unsatisfiable (PosFin 65) f9392 := by
  apply lratCheckerSound f9392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9392
  · intro a ha; simp [p9392] at ha; subst a; trivial
  · exact checked9392
theorem derived9392 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9392 := by
  apply localUnsat_implies_entails f9392 [c2547, c3144] c9392 unsat9392 (by rfl) a
  have h0 : Entails.eval a c2547 := h 2546 (by decide)
  have h1 : Entails.eval a c3144 := h 3143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9393 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9393 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9383, some c7994, some c8269, some c9390, some c3728, some c3748, some c9284, some c9352, some c3718, some c3733, some c9035, some c3744, some c9391, some c9392, some c3527, some c4917, some c4300, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9393 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9393 : lratChecker f9393 p9393 = .success := by decide +kernel
theorem unsat9393 : Unsatisfiable (PosFin 65) f9393 := by
  apply lratCheckerSound f9393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9393
  · intro a ha; simp [p9393] at ha; subst a; trivial
  · exact checked9393
theorem derived9393 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9393 := by
  apply localUnsat_implies_entails f9393 [c9347, c9383, c7994, c8269, c9390, c3728, c3748, c9284, c9352, c3718, c3733, c9035, c3744, c9391, c9392, c3527, c4917, c4300] c9393 unsat9393 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9383 := derived9383 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c9390 := derived9390 a h
  have h5 : Entails.eval a c3728 := h 3727 (by decide)
  have h6 : Entails.eval a c3748 := h 3747 (by decide)
  have h7 : Entails.eval a c9284 := derived9284 a h
  have h8 : Entails.eval a c9352 := derived9352 a h
  have h9 : Entails.eval a c3718 := h 3717 (by decide)
  have h10 : Entails.eval a c3733 := h 3732 (by decide)
  have h11 : Entails.eval a c9035 := derived9035 a h
  have h12 : Entails.eval a c3744 := h 3743 (by decide)
  have h13 : Entails.eval a c9391 := derived9391 a h
  have h14 : Entails.eval a c9392 := derived9392 a h
  have h15 : Entails.eval a c3527 := h 3526 (by decide)
  have h16 : Entails.eval a c4917 := h 4916 (by decide)
  have h17 : Entails.eval a c4300 := h 4299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9394 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9394 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9393, some c9347, some c9355, some c1222, some c3637, some c3639, some c3819, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9394 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9394 : lratChecker f9394 p9394 = .success := by decide +kernel
theorem unsat9394 : Unsatisfiable (PosFin 65) f9394 := by
  apply lratCheckerSound f9394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9394
  · intro a ha; simp [p9394] at ha; subst a; trivial
  · exact checked9394
theorem derived9394 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9394 := by
  apply localUnsat_implies_entails f9394 [c9393, c9347, c9355, c1222, c3637, c3639, c3819] c9394 unsat9394 (by rfl) a
  have h0 : Entails.eval a c9393 := derived9393 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9355 := derived9355 a h
  have h3 : Entails.eval a c1222 := h 1221 (by decide)
  have h4 : Entails.eval a c3637 := h 3636 (by decide)
  have h5 : Entails.eval a c3639 := h 3638 (by decide)
  have h6 : Entails.eval a c3819 := h 3818 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9395 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9395 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1418, some c9361, some c1428, some c1435, some c1218, some c1235, some c1229, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9395 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9395 : lratChecker f9395 p9395 = .success := by decide +kernel
theorem unsat9395 : Unsatisfiable (PosFin 65) f9395 := by
  apply lratCheckerSound f9395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9395
  · intro a ha; simp [p9395] at ha; subst a; trivial
  · exact checked9395
theorem derived9395 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9395 := by
  apply localUnsat_implies_entails f9395 [c1418, c9361, c1428, c1435, c1218, c1235, c1229] c9395 unsat9395 (by rfl) a
  have h0 : Entails.eval a c1418 := h 1417 (by decide)
  have h1 : Entails.eval a c9361 := derived9361 a h
  have h2 : Entails.eval a c1428 := h 1427 (by decide)
  have h3 : Entails.eval a c1435 := h 1434 (by decide)
  have h4 : Entails.eval a c1218 := h 1217 (by decide)
  have h5 : Entails.eval a c1235 := h 1234 (by decide)
  have h6 : Entails.eval a c1229 := h 1228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9396 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9396 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9357, some c9394, some c9395, some c9367, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9396 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9396 : lratChecker f9396 p9396 = .success := by decide +kernel
theorem unsat9396 : Unsatisfiable (PosFin 65) f9396 := by
  apply lratCheckerSound f9396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9396
  · intro a ha; simp [p9396] at ha; subst a; trivial
  · exact checked9396
theorem derived9396 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9396 := by
  apply localUnsat_implies_entails f9396 [c9357, c9394, c9395, c9367] c9396 unsat9396 (by rfl) a
  have h0 : Entails.eval a c9357 := derived9357 a h
  have h1 : Entails.eval a c9394 := derived9394 a h
  have h2 : Entails.eval a c9395 := derived9395 a h
  have h3 : Entails.eval a c9367 := derived9367 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9397 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9397 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4611, some c2876, some c3146, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9397 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9397 : lratChecker f9397 p9397 = .success := by decide +kernel
theorem unsat9397 : Unsatisfiable (PosFin 65) f9397 := by
  apply lratCheckerSound f9397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9397
  · intro a ha; simp [p9397] at ha; subst a; trivial
  · exact checked9397
theorem derived9397 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9397 := by
  apply localUnsat_implies_entails f9397 [c4611, c2876, c3146] c9397 unsat9397 (by rfl) a
  have h0 : Entails.eval a c4611 := h 4610 (by decide)
  have h1 : Entails.eval a c2876 := h 2875 (by decide)
  have h2 : Entails.eval a c3146 := h 3145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9398 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9398 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2682, some c2884, some c3157, some c3147, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9398 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9398 : lratChecker f9398 p9398 = .success := by decide +kernel
theorem unsat9398 : Unsatisfiable (PosFin 65) f9398 := by
  apply lratCheckerSound f9398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9398
  · intro a ha; simp [p9398] at ha; subst a; trivial
  · exact checked9398
theorem derived9398 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9398 := by
  apply localUnsat_implies_entails f9398 [c2682, c2884, c3157, c3147] c9398 unsat9398 (by rfl) a
  have h0 : Entails.eval a c2682 := h 2681 (by decide)
  have h1 : Entails.eval a c2884 := h 2883 (by decide)
  have h2 : Entails.eval a c3157 := h 3156 (by decide)
  have h3 : Entails.eval a c3147 := h 3146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9399 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9399 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c149, some c5480, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9399 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9399 : lratChecker f9399 p9399 = .success := by decide +kernel
theorem unsat9399 : Unsatisfiable (PosFin 65) f9399 := by
  apply lratCheckerSound f9399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9399
  · intro a ha; simp [p9399] at ha; subst a; trivial
  · exact checked9399
theorem derived9399 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9399 := by
  apply localUnsat_implies_entails f9399 [c149, c5480] c9399 unsat9399 (by rfl) a
  have h0 : Entails.eval a c149 := h 148 (by decide)
  have h1 : Entails.eval a c5480 := h 5479 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9400 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9400 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9398, some c9115, some c9195, some c8496, some c8580, some c9369, some c9399, some c3632, some c2911, some c3147, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9400 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9400 : lratChecker f9400 p9400 = .success := by decide +kernel
theorem unsat9400 : Unsatisfiable (PosFin 65) f9400 := by
  apply lratCheckerSound f9400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9400
  · intro a ha; simp [p9400] at ha; subst a; trivial
  · exact checked9400
theorem derived9400 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9400 := by
  apply localUnsat_implies_entails f9400 [c9347, c9398, c9115, c9195, c8496, c8580, c9369, c9399, c3632, c2911, c3147] c9400 unsat9400 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9398 := derived9398 a h
  have h2 : Entails.eval a c9115 := derived9115 a h
  have h3 : Entails.eval a c9195 := derived9195 a h
  have h4 : Entails.eval a c8496 := derived8496 a h
  have h5 : Entails.eval a c8580 := derived8580 a h
  have h6 : Entails.eval a c9369 := derived9369 a h
  have h7 : Entails.eval a c9399 := derived9399 a h
  have h8 : Entails.eval a c3632 := h 3631 (by decide)
  have h9 : Entails.eval a c2911 := h 2910 (by decide)
  have h10 : Entails.eval a c3147 := h 3146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9401 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨58, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9401 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c2682, some c2884, some c3147, some c3171, some c3163, some c1378, some c2851, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9401 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9401 : lratChecker f9401 p9401 = .success := by decide +kernel
theorem unsat9401 : Unsatisfiable (PosFin 65) f9401 := by
  apply lratCheckerSound f9401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9401
  · intro a ha; simp [p9401] at ha; subst a; trivial
  · exact checked9401
theorem derived9401 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9401 := by
  apply localUnsat_implies_entails f9401 [c9347, c2682, c2884, c3147, c3171, c3163, c1378, c2851] c9401 unsat9401 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c2682 := h 2681 (by decide)
  have h2 : Entails.eval a c2884 := h 2883 (by decide)
  have h3 : Entails.eval a c3147 := h 3146 (by decide)
  have h4 : Entails.eval a c3171 := h 3170 (by decide)
  have h5 : Entails.eval a c3163 := h 3162 (by decide)
  have h6 : Entails.eval a c1378 := h 1377 (by decide)
  have h7 : Entails.eval a c2851 := h 2850 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9402 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨63, by decide⟩, true), (⟨7, by decide⟩, false), (⟨58, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9402 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2893, some c3172, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9402 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9402 : lratChecker f9402 p9402 = .success := by decide +kernel
theorem unsat9402 : Unsatisfiable (PosFin 65) f9402 := by
  apply lratCheckerSound f9402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9402
  · intro a ha; simp [p9402] at ha; subst a; trivial
  · exact checked9402
theorem derived9402 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9402 := by
  apply localUnsat_implies_entails f9402 [c2893, c3172] c9402 unsat9402 (by rfl) a
  have h0 : Entails.eval a c2893 := h 2892 (by decide)
  have h1 : Entails.eval a c3172 := h 3171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9403 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨7, by decide⟩, false), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9403 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2873, some c3139, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9403 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9403 : lratChecker f9403 p9403 = .success := by decide +kernel
theorem unsat9403 : Unsatisfiable (PosFin 65) f9403 := by
  apply lratCheckerSound f9403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9403
  · intro a ha; simp [p9403] at ha; subst a; trivial
  · exact checked9403
theorem derived9403 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9403 := by
  apply localUnsat_implies_entails f9403 [c2873, c3139] c9403 unsat9403 (by rfl) a
  have h0 : Entails.eval a c2873 := h 2872 (by decide)
  have h1 : Entails.eval a c3139 := h 3138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9404 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9404 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9357, some c9393, some c9347, some c9396, some c9397, some c9400, some c9401, some c9115, some c9195, some c8496, some c8580, some c9369, some c9403, some c907, some c5498, some c5484, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9404 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9404 : lratChecker f9404 p9404 = .success := by decide +kernel
theorem unsat9404 : Unsatisfiable (PosFin 65) f9404 := by
  apply lratCheckerSound f9404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9404
  · intro a ha; simp [p9404] at ha; subst a; trivial
  · exact checked9404
theorem derived9404 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9404 := by
  apply localUnsat_implies_entails f9404 [c9357, c9393, c9347, c9396, c9397, c9400, c9401, c9115, c9195, c8496, c8580, c9369, c9403, c907, c5498, c5484] c9404 unsat9404 (by rfl) a
  have h0 : Entails.eval a c9357 := derived9357 a h
  have h1 : Entails.eval a c9393 := derived9393 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9396 := derived9396 a h
  have h4 : Entails.eval a c9397 := derived9397 a h
  have h5 : Entails.eval a c9400 := derived9400 a h
  have h6 : Entails.eval a c9401 := derived9401 a h
  have h7 : Entails.eval a c9115 := derived9115 a h
  have h8 : Entails.eval a c9195 := derived9195 a h
  have h9 : Entails.eval a c8496 := derived8496 a h
  have h10 : Entails.eval a c8580 := derived8580 a h
  have h11 : Entails.eval a c9369 := derived9369 a h
  have h12 : Entails.eval a c9403 := derived9403 a h
  have h13 : Entails.eval a c907 := h 906 (by decide)
  have h14 : Entails.eval a c5498 := h 5497 (by decide)
  have h15 : Entails.eval a c5484 := h 5483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9405 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9405 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9389, some c9372, some c9395, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9405 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9405 : lratChecker f9405 p9405 = .success := by decide +kernel
theorem unsat9405 : Unsatisfiable (PosFin 65) f9405 := by
  apply lratCheckerSound f9405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9405
  · intro a ha; simp [p9405] at ha; subst a; trivial
  · exact checked9405
theorem derived9405 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9405 := by
  apply localUnsat_implies_entails f9405 [c9389, c9372, c9395] c9405 unsat9405 (by rfl) a
  have h0 : Entails.eval a c9389 := derived9389 a h
  have h1 : Entails.eval a c9372 := derived9372 a h
  have h2 : Entails.eval a c9395 := derived9395 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9406 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9406 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2844, some c2851, some c2861, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9406 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9406 : lratChecker f9406 p9406 = .success := by decide +kernel
theorem unsat9406 : Unsatisfiable (PosFin 65) f9406 := by
  apply lratCheckerSound f9406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9406
  · intro a ha; simp [p9406] at ha; subst a; trivial
  · exact checked9406
theorem derived9406 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9406 := by
  apply localUnsat_implies_entails f9406 [c2844, c2851, c2861] c9406 unsat9406 (by rfl) a
  have h0 : Entails.eval a c2844 := h 2843 (by decide)
  have h1 : Entails.eval a c2851 := h 2850 (by decide)
  have h2 : Entails.eval a c2861 := h 2860 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9407 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9407 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9357, some c9404, some c8420, some c9405, some c9406, some c2838, some c2857, some c2854, some c2887, some c2688, some c3161, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9407 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9407 : lratChecker f9407 p9407 = .success := by decide +kernel
theorem unsat9407 : Unsatisfiable (PosFin 65) f9407 := by
  apply lratCheckerSound f9407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9407
  · intro a ha; simp [p9407] at ha; subst a; trivial
  · exact checked9407
theorem derived9407 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9407 := by
  apply localUnsat_implies_entails f9407 [c9347, c9357, c9404, c8420, c9405, c9406, c2838, c2857, c2854, c2887, c2688, c3161] c9407 unsat9407 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9357 := derived9357 a h
  have h2 : Entails.eval a c9404 := derived9404 a h
  have h3 : Entails.eval a c8420 := derived8420 a h
  have h4 : Entails.eval a c9405 := derived9405 a h
  have h5 : Entails.eval a c9406 := derived9406 a h
  have h6 : Entails.eval a c2838 := h 2837 (by decide)
  have h7 : Entails.eval a c2857 := h 2856 (by decide)
  have h8 : Entails.eval a c2854 := h 2853 (by decide)
  have h9 : Entails.eval a c2887 := h 2886 (by decide)
  have h10 : Entails.eval a c2688 := h 2687 (by decide)
  have h11 : Entails.eval a c3161 := h 3160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9408 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, false), (⟨4, by decide⟩, true), (⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9408 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3725, some c3734, some c3744, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9408 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9408 : lratChecker f9408 p9408 = .success := by decide +kernel
theorem unsat9408 : Unsatisfiable (PosFin 65) f9408 := by
  apply lratCheckerSound f9408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9408
  · intro a ha; simp [p9408] at ha; subst a; trivial
  · exact checked9408
theorem derived9408 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9408 := by
  apply localUnsat_implies_entails f9408 [c3725, c3734, c3744] c9408 unsat9408 (by rfl) a
  have h0 : Entails.eval a c3725 := h 3724 (by decide)
  have h1 : Entails.eval a c3734 := h 3733 (by decide)
  have h2 : Entails.eval a c3744 := h 3743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9409 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨58, by decide⟩, false), (⟨4, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9409 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9408, some c3718, some c8007, some c3727, some c3746, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9409 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9409 : lratChecker f9409 p9409 = .success := by decide +kernel
theorem unsat9409 : Unsatisfiable (PosFin 65) f9409 := by
  apply lratCheckerSound f9409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9409
  · intro a ha; simp [p9409] at ha; subst a; trivial
  · exact checked9409
theorem derived9409 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9409 := by
  apply localUnsat_implies_entails f9409 [c9408, c3718, c8007, c3727, c3746] c9409 unsat9409 (by rfl) a
  have h0 : Entails.eval a c9408 := derived9408 a h
  have h1 : Entails.eval a c3718 := h 3717 (by decide)
  have h2 : Entails.eval a c8007 := derived8007 a h
  have h3 : Entails.eval a c3727 := h 3726 (by decide)
  have h4 : Entails.eval a c3746 := h 3745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9410 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨4, by decide⟩, true), (⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9410 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3734, some c3737, some c3744, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9410 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9410 : lratChecker f9410 p9410 = .success := by decide +kernel
theorem unsat9410 : Unsatisfiable (PosFin 65) f9410 := by
  apply lratCheckerSound f9410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9410
  · intro a ha; simp [p9410] at ha; subst a; trivial
  · exact checked9410
theorem derived9410 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9410 := by
  apply localUnsat_implies_entails f9410 [c3734, c3737, c3744] c9410 unsat9410 (by rfl) a
  have h0 : Entails.eval a c3734 := h 3733 (by decide)
  have h1 : Entails.eval a c3737 := h 3736 (by decide)
  have h2 : Entails.eval a c3744 := h 3743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9411 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9411 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9378, some c9409, some c9410, some c9115, some c9377, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9411 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9411 : lratChecker f9411 p9411 = .success := by decide +kernel
theorem unsat9411 : Unsatisfiable (PosFin 65) f9411 := by
  apply lratCheckerSound f9411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9411
  · intro a ha; simp [p9411] at ha; subst a; trivial
  · exact checked9411
theorem derived9411 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9411 := by
  apply localUnsat_implies_entails f9411 [c9378, c9409, c9410, c9115, c9377] c9411 unsat9411 (by rfl) a
  have h0 : Entails.eval a c9378 := derived9378 a h
  have h1 : Entails.eval a c9409 := derived9409 a h
  have h2 : Entails.eval a c9410 := derived9410 a h
  have h3 : Entails.eval a c9115 := derived9115 a h
  have h4 : Entails.eval a c9377 := derived9377 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9412 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9412 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9411, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9412 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9412 : lratChecker f9412 p9412 = .success := by decide +kernel
theorem unsat9412 : Unsatisfiable (PosFin 65) f9412 := by
  apply lratCheckerSound f9412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9412
  · intro a ha; simp [p9412] at ha; subst a; trivial
  · exact checked9412
theorem derived9412 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9412 := by
  apply localUnsat_implies_entails f9412 [c9407, c9411] c9412 unsat9412 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9411 := derived9411 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9413 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9413 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9394, some c9397, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9413 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9413 : lratChecker f9413 p9413 = .success := by decide +kernel
theorem unsat9413 : Unsatisfiable (PosFin 65) f9413 := by
  apply lratCheckerSound f9413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9413
  · intro a ha; simp [p9413] at ha; subst a; trivial
  · exact checked9413
theorem derived9413 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9413 := by
  apply localUnsat_implies_entails f9413 [c9347, c9394, c9397] c9413 unsat9413 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9394 := derived9394 a h
  have h2 : Entails.eval a c9397 := derived9397 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9414 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9414 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9412, some c8269, some c7994, some c9393, some c9347, some c9413, some c8420, some c9389, some c2853, some c2858, some c2859, some c3691, some c4263, some c4076, some c2880, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9414 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9414 : lratChecker f9414 p9414 = .success := by decide +kernel
theorem unsat9414 : Unsatisfiable (PosFin 65) f9414 := by
  apply lratCheckerSound f9414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9414
  · intro a ha; simp [p9414] at ha; subst a; trivial
  · exact checked9414
theorem derived9414 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9414 := by
  apply localUnsat_implies_entails f9414 [c9412, c8269, c7994, c9393, c9347, c9413, c8420, c9389, c2853, c2858, c2859, c3691, c4263, c4076, c2880] c9414 unsat9414 (by rfl) a
  have h0 : Entails.eval a c9412 := derived9412 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c9393 := derived9393 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c9413 := derived9413 a h
  have h6 : Entails.eval a c8420 := derived8420 a h
  have h7 : Entails.eval a c9389 := derived9389 a h
  have h8 : Entails.eval a c2853 := h 2852 (by decide)
  have h9 : Entails.eval a c2858 := h 2857 (by decide)
  have h10 : Entails.eval a c2859 := h 2858 (by decide)
  have h11 : Entails.eval a c3691 := h 3690 (by decide)
  have h12 : Entails.eval a c4263 := h 4262 (by decide)
  have h13 : Entails.eval a c4076 := h 4075 (by decide)
  have h14 : Entails.eval a c2880 := h 2879 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9415 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9415 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c9347, some c9385, some c9386, some c9402, some c8416, some c2856, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9415 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9415 : lratChecker f9415 p9415 = .success := by decide +kernel
theorem unsat9415 : Unsatisfiable (PosFin 65) f9415 := by
  apply lratCheckerSound f9415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9415
  · intro a ha; simp [p9415] at ha; subst a; trivial
  · exact checked9415
theorem derived9415 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9415 := by
  apply localUnsat_implies_entails f9415 [c7994, c9347, c9385, c9386, c9402, c8416, c2856] c9415 unsat9415 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9385 := derived9385 a h
  have h3 : Entails.eval a c9386 := derived9386 a h
  have h4 : Entails.eval a c9402 := derived9402 a h
  have h5 : Entails.eval a c8416 := derived8416 a h
  have h6 : Entails.eval a c2856 := h 2855 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9416 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9416 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2853, some c2858, some c2859, some c2863, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p9416 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9416 : lratChecker f9416 p9416 = .success := by decide +kernel
theorem unsat9416 : Unsatisfiable (PosFin 65) f9416 := by
  apply lratCheckerSound f9416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9416
  · intro a ha; simp [p9416] at ha; subst a; trivial
  · exact checked9416
theorem derived9416 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9416 := by
  apply localUnsat_implies_entails f9416 [c2853, c2858, c2859, c2863] c9416 unsat9416 (by rfl) a
  have h0 : Entails.eval a c2853 := h 2852 (by decide)
  have h1 : Entails.eval a c2858 := h 2857 (by decide)
  have h2 : Entails.eval a c2859 := h 2858 (by decide)
  have h3 : Entails.eval a c2863 := h 2862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9417 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9417 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9412, some c8269, some c7994, some c9347, some c9414, some c9415, some c8420, some c9389, some c9416, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9417 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9417 : lratChecker f9417 p9417 = .success := by decide +kernel
theorem unsat9417 : Unsatisfiable (PosFin 65) f9417 := by
  apply lratCheckerSound f9417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9417
  · intro a ha; simp [p9417] at ha; subst a; trivial
  · exact checked9417
theorem derived9417 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9417 := by
  apply localUnsat_implies_entails f9417 [c9412, c8269, c7994, c9347, c9414, c9415, c8420, c9389, c9416] c9417 unsat9417 (by rfl) a
  have h0 : Entails.eval a c9412 := derived9412 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9414 := derived9414 a h
  have h5 : Entails.eval a c9415 := derived9415 a h
  have h6 : Entails.eval a c8420 := derived8420 a h
  have h7 : Entails.eval a c9389 := derived9389 a h
  have h8 : Entails.eval a c9416 := derived9416 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9418 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨58, by decide⟩, false), (⟨56, by decide⟩, true), (⟨63, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9418 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2677, some c2695, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9418 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9418 : lratChecker f9418 p9418 = .success := by decide +kernel
theorem unsat9418 : Unsatisfiable (PosFin 65) f9418 := by
  apply lratCheckerSound f9418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9418
  · intro a ha; simp [p9418] at ha; subst a; trivial
  · exact checked9418
theorem derived9418 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9418 := by
  apply localUnsat_implies_entails f9418 [c2677, c2695] c9418 unsat9418 (by rfl) a
  have h0 : Entails.eval a c2677 := h 2676 (by decide)
  have h1 : Entails.eval a c2695 := h 2694 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9419 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9419 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9412, some c7994, some c8269, some c9417, some c3728, some c3748, some c9284, some c8296, some c3718, some c3733, some c9035, some c3744, some c9416, some c9418, some c9392, some c3527, some c4300, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9419 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9419 : lratChecker f9419 p9419 = .success := by decide +kernel
theorem unsat9419 : Unsatisfiable (PosFin 65) f9419 := by
  apply lratCheckerSound f9419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9419
  · intro a ha; simp [p9419] at ha; subst a; trivial
  · exact checked9419
theorem derived9419 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9419 := by
  apply localUnsat_implies_entails f9419 [c9347, c9412, c7994, c8269, c9417, c3728, c3748, c9284, c8296, c3718, c3733, c9035, c3744, c9416, c9418, c9392, c3527, c4300] c9419 unsat9419 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9412 := derived9412 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c9417 := derived9417 a h
  have h5 : Entails.eval a c3728 := h 3727 (by decide)
  have h6 : Entails.eval a c3748 := h 3747 (by decide)
  have h7 : Entails.eval a c9284 := derived9284 a h
  have h8 : Entails.eval a c8296 := derived8296 a h
  have h9 : Entails.eval a c3718 := h 3717 (by decide)
  have h10 : Entails.eval a c3733 := h 3732 (by decide)
  have h11 : Entails.eval a c9035 := derived9035 a h
  have h12 : Entails.eval a c3744 := h 3743 (by decide)
  have h13 : Entails.eval a c9416 := derived9416 a h
  have h14 : Entails.eval a c9418 := derived9418 a h
  have h15 : Entails.eval a c9392 := derived9392 a h
  have h16 : Entails.eval a c3527 := h 3526 (by decide)
  have h17 : Entails.eval a c4300 := h 4299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9420 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9420 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2506, some c3236, some c3637, some c3639, some c3664, some c3818, some c3660, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9420 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9420 : lratChecker f9420 p9420 = .success := by decide +kernel
theorem unsat9420 : Unsatisfiable (PosFin 65) f9420 := by
  apply lratCheckerSound f9420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9420
  · intro a ha; simp [p9420] at ha; subst a; trivial
  · exact checked9420
theorem derived9420 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9420 := by
  apply localUnsat_implies_entails f9420 [c2506, c3236, c3637, c3639, c3664, c3818, c3660] c9420 unsat9420 (by rfl) a
  have h0 : Entails.eval a c2506 := h 2505 (by decide)
  have h1 : Entails.eval a c3236 := h 3235 (by decide)
  have h2 : Entails.eval a c3637 := h 3636 (by decide)
  have h3 : Entails.eval a c3639 := h 3638 (by decide)
  have h4 : Entails.eval a c3664 := h 3663 (by decide)
  have h5 : Entails.eval a c3818 := h 3817 (by decide)
  have h6 : Entails.eval a c3660 := h 3659 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9421 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9421 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9419, some c8435, some c8445, some c1413, some c3231, some c4540, some c4601, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9421 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9421 : lratChecker f9421 p9421 = .success := by decide +kernel
theorem unsat9421 : Unsatisfiable (PosFin 65) f9421 := by
  apply lratCheckerSound f9421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9421
  · intro a ha; simp [p9421] at ha; subst a; trivial
  · exact checked9421
theorem derived9421 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9421 := by
  apply localUnsat_implies_entails f9421 [c9419, c8435, c8445, c1413, c3231, c4540, c4601] c9421 unsat9421 (by rfl) a
  have h0 : Entails.eval a c9419 := derived9419 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8445 := derived8445 a h
  have h3 : Entails.eval a c1413 := h 1412 (by decide)
  have h4 : Entails.eval a c3231 := h 3230 (by decide)
  have h5 : Entails.eval a c4540 := h 4539 (by decide)
  have h6 : Entails.eval a c4601 := h 4600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9422 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9422 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9419, some c9421, some c9195, some c8580, some c9251, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9422 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9422 : lratChecker f9422 p9422 = .success := by decide +kernel
theorem unsat9422 : Unsatisfiable (PosFin 65) f9422 := by
  apply lratCheckerSound f9422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9422
  · intro a ha; simp [p9422] at ha; subst a; trivial
  · exact checked9422
theorem derived9422 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9422 := by
  apply localUnsat_implies_entails f9422 [c9419, c9421, c9195, c8580, c9251] c9422 unsat9422 (by rfl) a
  have h0 : Entails.eval a c9419 := derived9419 a h
  have h1 : Entails.eval a c9421 := derived9421 a h
  have h2 : Entails.eval a c9195 := derived9195 a h
  have h3 : Entails.eval a c8580 := derived8580 a h
  have h4 : Entails.eval a c9251 := derived9251 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9423 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9423 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8435, some c8445, some c1413, some c690, some c8580, some c930, some c4601, some c4592, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9423 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9423 : lratChecker f9423 p9423 = .success := by decide +kernel
theorem unsat9423 : Unsatisfiable (PosFin 65) f9423 := by
  apply lratCheckerSound f9423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9423
  · intro a ha; simp [p9423] at ha; subst a; trivial
  · exact checked9423
theorem derived9423 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9423 := by
  apply localUnsat_implies_entails f9423 [c8435, c8445, c1413, c690, c8580, c930, c4601, c4592] c9423 unsat9423 (by rfl) a
  have h0 : Entails.eval a c8435 := derived8435 a h
  have h1 : Entails.eval a c8445 := derived8445 a h
  have h2 : Entails.eval a c1413 := h 1412 (by decide)
  have h3 : Entails.eval a c690 := h 689 (by decide)
  have h4 : Entails.eval a c8580 := derived8580 a h
  have h5 : Entails.eval a c930 := h 929 (by decide)
  have h6 : Entails.eval a c4601 := h 4600 (by decide)
  have h7 : Entails.eval a c4592 := h 4591 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9424 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9424 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9422, some c9423, some c9195, some c8580, some c4580, some c907, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9424 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9424 : lratChecker f9424 p9424 = .success := by decide +kernel
theorem unsat9424 : Unsatisfiable (PosFin 65) f9424 := by
  apply lratCheckerSound f9424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9424
  · intro a ha; simp [p9424] at ha; subst a; trivial
  · exact checked9424
theorem derived9424 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9424 := by
  apply localUnsat_implies_entails f9424 [c9422, c9423, c9195, c8580, c4580, c907] c9424 unsat9424 (by rfl) a
  have h0 : Entails.eval a c9422 := derived9422 a h
  have h1 : Entails.eval a c9423 := derived9423 a h
  have h2 : Entails.eval a c9195 := derived9195 a h
  have h3 : Entails.eval a c8580 := derived8580 a h
  have h4 : Entails.eval a c4580 := h 4579 (by decide)
  have h5 : Entails.eval a c907 := h 906 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9425 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9425 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8435, some c8445, some c891, some c3227, some c3230, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9425 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9425 : lratChecker f9425 p9425 = .success := by decide +kernel
theorem unsat9425 : Unsatisfiable (PosFin 65) f9425 := by
  apply lratCheckerSound f9425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9425
  · intro a ha; simp [p9425] at ha; subst a; trivial
  · exact checked9425
theorem derived9425 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9425 := by
  apply localUnsat_implies_entails f9425 [c8435, c8445, c891, c3227, c3230] c9425 unsat9425 (by rfl) a
  have h0 : Entails.eval a c8435 := derived8435 a h
  have h1 : Entails.eval a c8445 := derived8445 a h
  have h2 : Entails.eval a c891 := h 890 (by decide)
  have h3 : Entails.eval a c3227 := h 3226 (by decide)
  have h4 : Entails.eval a c3230 := h 3229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9426 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9426 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9425, some c9195, some c8580, some c9251, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9426 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9426 : lratChecker f9426 p9426 = .success := by decide +kernel
theorem unsat9426 : Unsatisfiable (PosFin 65) f9426 := by
  apply lratCheckerSound f9426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9426
  · intro a ha; simp [p9426] at ha; subst a; trivial
  · exact checked9426
theorem derived9426 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9426 := by
  apply localUnsat_implies_entails f9426 [c9425, c9195, c8580, c9251] c9426 unsat9426 (by rfl) a
  have h0 : Entails.eval a c9425 := derived9425 a h
  have h1 : Entails.eval a c9195 := derived9195 a h
  have h2 : Entails.eval a c8580 := derived8580 a h
  have h3 : Entails.eval a c9251 := derived9251 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9427 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9427 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8435, some c8445, some c891, some c892, some c938, some c940, some c930, some c698, some c695, some c905, some c1401, some c1400, some c717, some c1417, some c944, some c93, some c877, some c896, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9427 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9427 : lratChecker f9427 p9427 = .success := by decide +kernel
theorem unsat9427 : Unsatisfiable (PosFin 65) f9427 := by
  apply lratCheckerSound f9427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9427
  · intro a ha; simp [p9427] at ha; subst a; trivial
  · exact checked9427
theorem derived9427 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9427 := by
  apply localUnsat_implies_entails f9427 [c8435, c8445, c891, c892, c938, c940, c930, c698, c695, c905, c1401, c1400, c717, c1417, c944, c93, c877, c896] c9427 unsat9427 (by rfl) a
  have h0 : Entails.eval a c8435 := derived8435 a h
  have h1 : Entails.eval a c8445 := derived8445 a h
  have h2 : Entails.eval a c891 := h 890 (by decide)
  have h3 : Entails.eval a c892 := h 891 (by decide)
  have h4 : Entails.eval a c938 := h 937 (by decide)
  have h5 : Entails.eval a c940 := h 939 (by decide)
  have h6 : Entails.eval a c930 := h 929 (by decide)
  have h7 : Entails.eval a c698 := h 697 (by decide)
  have h8 : Entails.eval a c695 := h 694 (by decide)
  have h9 : Entails.eval a c905 := h 904 (by decide)
  have h10 : Entails.eval a c1401 := h 1400 (by decide)
  have h11 : Entails.eval a c1400 := h 1399 (by decide)
  have h12 : Entails.eval a c717 := h 716 (by decide)
  have h13 : Entails.eval a c1417 := h 1416 (by decide)
  have h14 : Entails.eval a c944 := h 943 (by decide)
  have h15 : Entails.eval a c93 := h 92 (by decide)
  have h16 : Entails.eval a c877 := h 876 (by decide)
  have h17 : Entails.eval a c896 := h 895 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9428 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9428 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9419, some c9420, some c1433, some c9230, some c9210, some c1439, some c1423, some c1447, some c1437, some c1449, some c9424, some c9426, some c9427, some c9195, some c8496, some c8580, some c1403, some c8609, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9428 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9428 : lratChecker f9428 p9428 = .success := by decide +kernel
theorem unsat9428 : Unsatisfiable (PosFin 65) f9428 := by
  apply lratCheckerSound f9428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9428
  · intro a ha; simp [p9428] at ha; subst a; trivial
  · exact checked9428
theorem derived9428 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9428 := by
  apply localUnsat_implies_entails f9428 [c9347, c9419, c9420, c1433, c9230, c9210, c1439, c1423, c1447, c1437, c1449, c9424, c9426, c9427, c9195, c8496, c8580, c1403, c8609] c9428 unsat9428 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9419 := derived9419 a h
  have h2 : Entails.eval a c9420 := derived9420 a h
  have h3 : Entails.eval a c1433 := h 1432 (by decide)
  have h4 : Entails.eval a c9230 := derived9230 a h
  have h5 : Entails.eval a c9210 := derived9210 a h
  have h6 : Entails.eval a c1439 := h 1438 (by decide)
  have h7 : Entails.eval a c1423 := h 1422 (by decide)
  have h8 : Entails.eval a c1447 := h 1446 (by decide)
  have h9 : Entails.eval a c1437 := h 1436 (by decide)
  have h10 : Entails.eval a c1449 := h 1448 (by decide)
  have h11 : Entails.eval a c9424 := derived9424 a h
  have h12 : Entails.eval a c9426 := derived9426 a h
  have h13 : Entails.eval a c9427 := derived9427 a h
  have h14 : Entails.eval a c9195 := derived9195 a h
  have h15 : Entails.eval a c8496 := derived8496 a h
  have h16 : Entails.eval a c8580 := derived8580 a h
  have h17 : Entails.eval a c1403 := h 1402 (by decide)
  have h18 : Entails.eval a c8609 := derived8609 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9429 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9429 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9419, some c9347, some c9420, some c9230, some c9428, some c1452, some c1422, some c1426, some c2493, some c1387, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9429 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9429 : lratChecker f9429 p9429 = .success := by decide +kernel
theorem unsat9429 : Unsatisfiable (PosFin 65) f9429 := by
  apply lratCheckerSound f9429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9429
  · intro a ha; simp [p9429] at ha; subst a; trivial
  · exact checked9429
theorem derived9429 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9429 := by
  apply localUnsat_implies_entails f9429 [c9419, c9347, c9420, c9230, c9428, c1452, c1422, c1426, c2493, c1387] c9429 unsat9429 (by rfl) a
  have h0 : Entails.eval a c9419 := derived9419 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9420 := derived9420 a h
  have h3 : Entails.eval a c9230 := derived9230 a h
  have h4 : Entails.eval a c9428 := derived9428 a h
  have h5 : Entails.eval a c1452 := h 1451 (by decide)
  have h6 : Entails.eval a c1422 := h 1421 (by decide)
  have h7 : Entails.eval a c1426 := h 1425 (by decide)
  have h8 : Entails.eval a c2493 := h 2492 (by decide)
  have h9 : Entails.eval a c1387 := h 1386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9430 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9430 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2506, some c3236, some c2876, some c3637, some c4027, some c3639, some c3664, some c5008, some c4253, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9430 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9430 : lratChecker f9430 p9430 = .success := by decide +kernel
theorem unsat9430 : Unsatisfiable (PosFin 65) f9430 := by
  apply lratCheckerSound f9430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9430
  · intro a ha; simp [p9430] at ha; subst a; trivial
  · exact checked9430
theorem derived9430 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9430 := by
  apply localUnsat_implies_entails f9430 [c2506, c3236, c2876, c3637, c4027, c3639, c3664, c5008, c4253] c9430 unsat9430 (by rfl) a
  have h0 : Entails.eval a c2506 := h 2505 (by decide)
  have h1 : Entails.eval a c3236 := h 3235 (by decide)
  have h2 : Entails.eval a c2876 := h 2875 (by decide)
  have h3 : Entails.eval a c3637 := h 3636 (by decide)
  have h4 : Entails.eval a c4027 := h 4026 (by decide)
  have h5 : Entails.eval a c3639 := h 3638 (by decide)
  have h6 : Entails.eval a c3664 := h 3663 (by decide)
  have h7 : Entails.eval a c5008 := h 5007 (by decide)
  have h8 : Entails.eval a c4253 := h 4252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9431 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9431 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8435, some c8445, some c3231, some c4540, some c3230, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9431 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9431 : lratChecker f9431 p9431 = .success := by decide +kernel
theorem unsat9431 : Unsatisfiable (PosFin 65) f9431 := by
  apply lratCheckerSound f9431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9431
  · intro a ha; simp [p9431] at ha; subst a; trivial
  · exact checked9431
theorem derived9431 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9431 := by
  apply localUnsat_implies_entails f9431 [c8435, c8445, c3231, c4540, c3230] c9431 unsat9431 (by rfl) a
  have h0 : Entails.eval a c8435 := derived8435 a h
  have h1 : Entails.eval a c8445 := derived8445 a h
  have h2 : Entails.eval a c3231 := h 3230 (by decide)
  have h3 : Entails.eval a c4540 := h 4539 (by decide)
  have h4 : Entails.eval a c3230 := h 3229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9432 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9432 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9426, some c9431, some c9195, some c8580, some c9251, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9432 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9432 : lratChecker f9432 p9432 = .success := by decide +kernel
theorem unsat9432 : Unsatisfiable (PosFin 65) f9432 := by
  apply lratCheckerSound f9432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9432
  · intro a ha; simp [p9432] at ha; subst a; trivial
  · exact checked9432
theorem derived9432 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9432 := by
  apply localUnsat_implies_entails f9432 [c9426, c9431, c9195, c8580, c9251] c9432 unsat9432 (by rfl) a
  have h0 : Entails.eval a c9426 := derived9426 a h
  have h1 : Entails.eval a c9431 := derived9431 a h
  have h2 : Entails.eval a c9195 := derived9195 a h
  have h3 : Entails.eval a c8580 := derived8580 a h
  have h4 : Entails.eval a c9251 := derived9251 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9433 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9433 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3237, some c3235, some c3266, some c9432, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9433 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9433 : lratChecker f9433 p9433 = .success := by decide +kernel
theorem unsat9433 : Unsatisfiable (PosFin 65) f9433 := by
  apply lratCheckerSound f9433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9433
  · intro a ha; simp [p9433] at ha; subst a; trivial
  · exact checked9433
theorem derived9433 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9433 := by
  apply localUnsat_implies_entails f9433 [c3237, c3235, c3266, c9432] c9433 unsat9433 (by rfl) a
  have h0 : Entails.eval a c3237 := h 3236 (by decide)
  have h1 : Entails.eval a c3235 := h 3234 (by decide)
  have h2 : Entails.eval a c3266 := h 3265 (by decide)
  have h3 : Entails.eval a c9432 := derived9432 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9434 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9434 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c8435, some c8445, some c692, some c690, some c2668, some c4601, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9434 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9434 : lratChecker f9434 p9434 = .success := by decide +kernel
theorem unsat9434 : Unsatisfiable (PosFin 65) f9434 := by
  apply lratCheckerSound f9434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9434
  · intro a ha; simp [p9434] at ha; subst a; trivial
  · exact checked9434
theorem derived9434 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9434 := by
  apply localUnsat_implies_entails f9434 [c9347, c8435, c8445, c692, c690, c2668, c4601] c9434 unsat9434 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8445 := derived8445 a h
  have h3 : Entails.eval a c692 := h 691 (by decide)
  have h4 : Entails.eval a c690 := h 689 (by decide)
  have h5 : Entails.eval a c2668 := h 2667 (by decide)
  have h6 : Entails.eval a c4601 := h 4600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9435 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9435 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9419, some c9429, some c9430, some c2682, some c9434, some c9195, some c8496, some c8580, some c9369, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9435 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9435 : lratChecker f9435 p9435 = .success := by decide +kernel
theorem unsat9435 : Unsatisfiable (PosFin 65) f9435 := by
  apply lratCheckerSound f9435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9435
  · intro a ha; simp [p9435] at ha; subst a; trivial
  · exact checked9435
theorem derived9435 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9435 := by
  apply localUnsat_implies_entails f9435 [c9347, c9419, c9429, c9430, c2682, c9434, c9195, c8496, c8580, c9369] c9435 unsat9435 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9419 := derived9419 a h
  have h2 : Entails.eval a c9429 := derived9429 a h
  have h3 : Entails.eval a c9430 := derived9430 a h
  have h4 : Entails.eval a c2682 := h 2681 (by decide)
  have h5 : Entails.eval a c9434 := derived9434 a h
  have h6 : Entails.eval a c9195 := derived9195 a h
  have h7 : Entails.eval a c8496 := derived8496 a h
  have h8 : Entails.eval a c8580 := derived8580 a h
  have h9 : Entails.eval a c9369 := derived9369 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9436 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9436 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2460, some c4440, some c4282, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9436 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9436 : lratChecker f9436 p9436 = .success := by decide +kernel
theorem unsat9436 : Unsatisfiable (PosFin 65) f9436 := by
  apply lratCheckerSound f9436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9436
  · intro a ha; simp [p9436] at ha; subst a; trivial
  · exact checked9436
theorem derived9436 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9436 := by
  apply localUnsat_implies_entails f9436 [c2460, c4440, c4282] c9436 unsat9436 (by rfl) a
  have h0 : Entails.eval a c2460 := h 2459 (by decide)
  have h1 : Entails.eval a c4440 := h 4439 (by decide)
  have h2 : Entails.eval a c4282 := h 4281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9437 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9437 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c8435, some c8445, some c692, some c690, some c8580, some c705, some c684, some c703, some c656, some c698, some c9436, some c2461, some c4280, some c4439, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9437 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9437 : lratChecker f9437 p9437 = .success := by decide +kernel
theorem unsat9437 : Unsatisfiable (PosFin 65) f9437 := by
  apply lratCheckerSound f9437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9437
  · intro a ha; simp [p9437] at ha; subst a; trivial
  · exact checked9437
theorem derived9437 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9437 := by
  apply localUnsat_implies_entails f9437 [c9347, c8435, c8445, c692, c690, c8580, c705, c684, c703, c656, c698, c9436, c2461, c4280, c4439] c9437 unsat9437 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8445 := derived8445 a h
  have h3 : Entails.eval a c692 := h 691 (by decide)
  have h4 : Entails.eval a c690 := h 689 (by decide)
  have h5 : Entails.eval a c8580 := derived8580 a h
  have h6 : Entails.eval a c705 := h 704 (by decide)
  have h7 : Entails.eval a c684 := h 683 (by decide)
  have h8 : Entails.eval a c703 := h 702 (by decide)
  have h9 : Entails.eval a c656 := h 655 (by decide)
  have h10 : Entails.eval a c698 := h 697 (by decide)
  have h11 : Entails.eval a c9436 := derived9436 a h
  have h12 : Entails.eval a c2461 := h 2460 (by decide)
  have h13 : Entails.eval a c4280 := h 4279 (by decide)
  have h14 : Entails.eval a c4439 := h 4438 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9438 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨63, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9438 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9195, some c8580, some c8496, some c685, some c8609, some c676, some c5313, some c5469, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9438 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9438 : lratChecker f9438 p9438 = .success := by decide +kernel
theorem unsat9438 : Unsatisfiable (PosFin 65) f9438 := by
  apply lratCheckerSound f9438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9438
  · intro a ha; simp [p9438] at ha; subst a; trivial
  · exact checked9438
theorem derived9438 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9438 := by
  apply localUnsat_implies_entails f9438 [c9195, c8580, c8496, c685, c8609, c676, c5313, c5469] c9438 unsat9438 (by rfl) a
  have h0 : Entails.eval a c9195 := derived9195 a h
  have h1 : Entails.eval a c8580 := derived8580 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c685 := h 684 (by decide)
  have h4 : Entails.eval a c8609 := derived8609 a h
  have h5 : Entails.eval a c676 := h 675 (by decide)
  have h6 : Entails.eval a c5313 := h 5312 (by decide)
  have h7 : Entails.eval a c5469 := h 5468 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9439 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨63, by decide⟩, true), (⟨7, by decide⟩, false), (⟨58, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9439 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4472, some c353, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p9439 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9439 : lratChecker f9439 p9439 = .success := by decide +kernel
theorem unsat9439 : Unsatisfiable (PosFin 65) f9439 := by
  apply lratCheckerSound f9439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9439
  · intro a ha; simp [p9439] at ha; subst a; trivial
  · exact checked9439
theorem derived9439 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9439 := by
  apply localUnsat_implies_entails f9439 [c4472, c353] c9439 unsat9439 (by rfl) a
  have h0 : Entails.eval a c4472 := h 4471 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9440 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨58, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9440 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9195, some c8496, some c9347, some c9438, some c667, some c8510, some c8583, some c690, some c697, some c9439, some c2827, some c1321, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9440 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9440 : lratChecker f9440 p9440 = .success := by decide +kernel
theorem unsat9440 : Unsatisfiable (PosFin 65) f9440 := by
  apply lratCheckerSound f9440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9440
  · intro a ha; simp [p9440] at ha; subst a; trivial
  · exact checked9440
theorem derived9440 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9440 := by
  apply localUnsat_implies_entails f9440 [c9195, c8496, c9347, c9438, c667, c8510, c8583, c690, c697, c9439, c2827, c1321] c9440 unsat9440 (by rfl) a
  have h0 : Entails.eval a c9195 := derived9195 a h
  have h1 : Entails.eval a c8496 := derived8496 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9438 := derived9438 a h
  have h4 : Entails.eval a c667 := h 666 (by decide)
  have h5 : Entails.eval a c8510 := derived8510 a h
  have h6 : Entails.eval a c8583 := derived8583 a h
  have h7 : Entails.eval a c690 := h 689 (by decide)
  have h8 : Entails.eval a c697 := h 696 (by decide)
  have h9 : Entails.eval a c9439 := derived9439 a h
  have h10 : Entails.eval a c2827 := h 2826 (by decide)
  have h11 : Entails.eval a c1321 := h 1320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9441 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9441 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1369, some c1362, some c1387, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9441 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9441 : lratChecker f9441 p9441 = .success := by decide +kernel
theorem unsat9441 : Unsatisfiable (PosFin 65) f9441 := by
  apply lratCheckerSound f9441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9441
  · intro a ha; simp [p9441] at ha; subst a; trivial
  · exact checked9441
theorem derived9441 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9441 := by
  apply localUnsat_implies_entails f9441 [c1369, c1362, c1387] c9441 unsat9441 (by rfl) a
  have h0 : Entails.eval a c1369 := h 1368 (by decide)
  have h1 : Entails.eval a c1362 := h 1361 (by decide)
  have h2 : Entails.eval a c1387 := h 1386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9442 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9442 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8580, some c8496, some c9347, some c667, some c675, some c683, some c685, some c661, some c698, some c688, some c2829, some c2458, some c2824, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9442 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9442 : lratChecker f9442 p9442 = .success := by decide +kernel
theorem unsat9442 : Unsatisfiable (PosFin 65) f9442 := by
  apply lratCheckerSound f9442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9442
  · intro a ha; simp [p9442] at ha; subst a; trivial
  · exact checked9442
theorem derived9442 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9442 := by
  apply localUnsat_implies_entails f9442 [c8580, c8496, c9347, c667, c675, c683, c685, c661, c698, c688, c2829, c2458, c2824] c9442 unsat9442 (by rfl) a
  have h0 : Entails.eval a c8580 := derived8580 a h
  have h1 : Entails.eval a c8496 := derived8496 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c667 := h 666 (by decide)
  have h4 : Entails.eval a c675 := h 674 (by decide)
  have h5 : Entails.eval a c683 := h 682 (by decide)
  have h6 : Entails.eval a c685 := h 684 (by decide)
  have h7 : Entails.eval a c661 := h 660 (by decide)
  have h8 : Entails.eval a c698 := h 697 (by decide)
  have h9 : Entails.eval a c688 := h 687 (by decide)
  have h10 : Entails.eval a c2829 := h 2828 (by decide)
  have h11 : Entails.eval a c2458 := h 2457 (by decide)
  have h12 : Entails.eval a c2824 := h 2823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9443 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9443 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9419, some c9347, some c9210, some c9429, some c9430, some c9230, some c9433, some c9435, some c9437, some c9195, some c8580, some c9440, some c9441, some c2457, some c3295, some c3624, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9443 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9443 : lratChecker f9443 p9443 = .success := by decide +kernel
theorem unsat9443 : Unsatisfiable (PosFin 65) f9443 := by
  apply lratCheckerSound f9443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9443
  · intro a ha; simp [p9443] at ha; subst a; trivial
  · exact checked9443
theorem derived9443 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9443 := by
  apply localUnsat_implies_entails f9443 [c9419, c9347, c9210, c9429, c9430, c9230, c9433, c9435, c9437, c9195, c8580, c9440, c9441, c2457, c3295, c3624] c9443 unsat9443 (by rfl) a
  have h0 : Entails.eval a c9419 := derived9419 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9210 := derived9210 a h
  have h3 : Entails.eval a c9429 := derived9429 a h
  have h4 : Entails.eval a c9430 := derived9430 a h
  have h5 : Entails.eval a c9230 := derived9230 a h
  have h6 : Entails.eval a c9433 := derived9433 a h
  have h7 : Entails.eval a c9435 := derived9435 a h
  have h8 : Entails.eval a c9437 := derived9437 a h
  have h9 : Entails.eval a c9195 := derived9195 a h
  have h10 : Entails.eval a c8580 := derived8580 a h
  have h11 : Entails.eval a c9440 := derived9440 a h
  have h12 : Entails.eval a c9441 := derived9441 a h
  have h13 : Entails.eval a c2457 := h 2456 (by decide)
  have h14 : Entails.eval a c3295 := h 3294 (by decide)
  have h15 : Entails.eval a c3624 := h 3623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9444 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9444 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4619, some c4617, some c4620, some c1428, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9444 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9444 : lratChecker f9444 p9444 = .success := by decide +kernel
theorem unsat9444 : Unsatisfiable (PosFin 65) f9444 := by
  apply lratCheckerSound f9444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9444
  · intro a ha; simp [p9444] at ha; subst a; trivial
  · exact checked9444
theorem derived9444 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9444 := by
  apply localUnsat_implies_entails f9444 [c4619, c4617, c4620, c1428] c9444 unsat9444 (by rfl) a
  have h0 : Entails.eval a c4619 := h 4618 (by decide)
  have h1 : Entails.eval a c4617 := h 4616 (by decide)
  have h2 : Entails.eval a c4620 := h 4619 (by decide)
  have h3 : Entails.eval a c1428 := h 1427 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9445 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9445 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1428, some c1441, some c1440, some c1431, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9445 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9445 : lratChecker f9445 p9445 = .success := by decide +kernel
theorem unsat9445 : Unsatisfiable (PosFin 65) f9445 := by
  apply lratCheckerSound f9445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9445
  · intro a ha; simp [p9445] at ha; subst a; trivial
  · exact checked9445
theorem derived9445 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9445 := by
  apply localUnsat_implies_entails f9445 [c1428, c1441, c1440, c1431] c9445 unsat9445 (by rfl) a
  have h0 : Entails.eval a c1428 := h 1427 (by decide)
  have h1 : Entails.eval a c1441 := h 1440 (by decide)
  have h2 : Entails.eval a c1440 := h 1439 (by decide)
  have h3 : Entails.eval a c1431 := h 1430 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9446 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9446 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9443, some c9419, some c9444, some c9215, some c9445, some c4635, some c4632, some c1422, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9446 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9446 : lratChecker f9446 p9446 = .success := by decide +kernel
theorem unsat9446 : Unsatisfiable (PosFin 65) f9446 := by
  apply lratCheckerSound f9446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9446
  · intro a ha; simp [p9446] at ha; subst a; trivial
  · exact checked9446
theorem derived9446 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9446 := by
  apply localUnsat_implies_entails f9446 [c9443, c9419, c9444, c9215, c9445, c4635, c4632, c1422] c9446 unsat9446 (by rfl) a
  have h0 : Entails.eval a c9443 := derived9443 a h
  have h1 : Entails.eval a c9419 := derived9419 a h
  have h2 : Entails.eval a c9444 := derived9444 a h
  have h3 : Entails.eval a c9215 := derived9215 a h
  have h4 : Entails.eval a c9445 := derived9445 a h
  have h5 : Entails.eval a c4635 := h 4634 (by decide)
  have h6 : Entails.eval a c4632 := h 4631 (by decide)
  have h7 : Entails.eval a c1422 := h 1421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9447 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨50, by decide⟩, true), (⟨58, by decide⟩, false), (⟨52, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9447 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9213, some c3336, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9447 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9447 : lratChecker f9447 p9447 = .success := by decide +kernel
theorem unsat9447 : Unsatisfiable (PosFin 65) f9447 := by
  apply lratCheckerSound f9447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9447
  · intro a ha; simp [p9447] at ha; subst a; trivial
  · exact checked9447
theorem derived9447 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9447 := by
  apply localUnsat_implies_entails f9447 [c9213, c3336] c9447 unsat9447 (by rfl) a
  have h0 : Entails.eval a c9213 := derived9213 a h
  have h1 : Entails.eval a c3336 := h 3335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9448 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨50, by decide⟩, true), (⟨58, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9448 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9447, some c9445, some c3337, some c3637, some c3639, some c3818, some c3664, some c3817, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9448 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9448 : lratChecker f9448 p9448 = .success := by decide +kernel
theorem unsat9448 : Unsatisfiable (PosFin 65) f9448 := by
  apply lratCheckerSound f9448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9448
  · intro a ha; simp [p9448] at ha; subst a; trivial
  · exact checked9448
theorem derived9448 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9448 := by
  apply localUnsat_implies_entails f9448 [c9447, c9445, c3337, c3637, c3639, c3818, c3664, c3817] c9448 unsat9448 (by rfl) a
  have h0 : Entails.eval a c9447 := derived9447 a h
  have h1 : Entails.eval a c9445 := derived9445 a h
  have h2 : Entails.eval a c3337 := h 3336 (by decide)
  have h3 : Entails.eval a c3637 := h 3636 (by decide)
  have h4 : Entails.eval a c3639 := h 3638 (by decide)
  have h5 : Entails.eval a c3818 := h 3817 (by decide)
  have h6 : Entails.eval a c3664 := h 3663 (by decide)
  have h7 : Entails.eval a c3817 := h 3816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9449 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨58, by decide⟩, false), (⟨1, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9449 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9448, some c3245, some c3246, some c9445, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9449 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9449 : lratChecker f9449 p9449 = .success := by decide +kernel
theorem unsat9449 : Unsatisfiable (PosFin 65) f9449 := by
  apply lratCheckerSound f9449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9449
  · intro a ha; simp [p9449] at ha; subst a; trivial
  · exact checked9449
theorem derived9449 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9449 := by
  apply localUnsat_implies_entails f9449 [c9448, c3245, c3246, c9445] c9449 unsat9449 (by rfl) a
  have h0 : Entails.eval a c9448 := derived9448 a h
  have h1 : Entails.eval a c3245 := h 3244 (by decide)
  have h2 : Entails.eval a c3246 := h 3245 (by decide)
  have h3 : Entails.eval a c9445 := derived9445 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9450 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨58, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9450 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9449, some c9215, some c9445, some c9249, some c9347, some c2483, some c3345, some c3785, some c3577, some c1387, some c3664, some c3817, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9450 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9450 : lratChecker f9450 p9450 = .success := by decide +kernel
theorem unsat9450 : Unsatisfiable (PosFin 65) f9450 := by
  apply lratCheckerSound f9450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9450
  · intro a ha; simp [p9450] at ha; subst a; trivial
  · exact checked9450
theorem derived9450 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9450 := by
  apply localUnsat_implies_entails f9450 [c9449, c9215, c9445, c9249, c9347, c2483, c3345, c3785, c3577, c1387, c3664, c3817] c9450 unsat9450 (by rfl) a
  have h0 : Entails.eval a c9449 := derived9449 a h
  have h1 : Entails.eval a c9215 := derived9215 a h
  have h2 : Entails.eval a c9445 := derived9445 a h
  have h3 : Entails.eval a c9249 := derived9249 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c2483 := h 2482 (by decide)
  have h6 : Entails.eval a c3345 := h 3344 (by decide)
  have h7 : Entails.eval a c3785 := h 3784 (by decide)
  have h8 : Entails.eval a c3577 := h 3576 (by decide)
  have h9 : Entails.eval a c1387 := h 1386 (by decide)
  have h10 : Entails.eval a c3664 := h 3663 (by decide)
  have h11 : Entails.eval a c3817 := h 3816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9450

end CochromaticTwenty.Certificates.FixedCore0
