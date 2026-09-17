import MerLeanExperiment.Certificates.Z12Direct_5_8_1.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_8_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c341 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f341 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c340, some c338, some c285, some c50, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p341 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked341 : lratChecker f341 p341 = .success := by decide +kernel
theorem unsat341 : Unsatisfiable (PosFin 31) f341 := by
  apply lratCheckerSound f341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p341
  · intro a ha; simp [p341] at ha; subst a; trivial
  · exact checked341
theorem derived341 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c341 := by
  apply localUnsat_implies_entails f341 [c340, c338, c285, c50] c341 unsat341 (by rfl) a
  have h0 : Entails.eval a c340 := derived340 a h
  have h1 : Entails.eval a c338 := derived338 a h
  have h2 : Entails.eval a c285 := derived285 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c342 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f342 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c341, some c340, some c285, some c112, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p342 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked342 : lratChecker f342 p342 = .success := by decide +kernel
theorem unsat342 : Unsatisfiable (PosFin 31) f342 := by
  apply lratCheckerSound f342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p342
  · intro a ha; simp [p342] at ha; subst a; trivial
  · exact checked342
theorem derived342 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c342 := by
  apply localUnsat_implies_entails f342 [c341, c340, c285, c112] c342 unsat342 (by rfl) a
  have h0 : Entails.eval a c341 := derived341 a h
  have h1 : Entails.eval a c340 := derived340 a h
  have h2 : Entails.eval a c285 := derived285 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c343 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f343 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c341, some c338, some c331, some c256, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p343 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked343 : lratChecker f343 p343 = .success := by decide +kernel
theorem unsat343 : Unsatisfiable (PosFin 31) f343 := by
  apply lratCheckerSound f343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p343
  · intro a ha; simp [p343] at ha; subst a; trivial
  · exact checked343
theorem derived343 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c343 := by
  apply localUnsat_implies_entails f343 [c341, c338, c331, c256] c343 unsat343 (by rfl) a
  have h0 : Entails.eval a c341 := derived341 a h
  have h1 : Entails.eval a c338 := derived338 a h
  have h2 : Entails.eval a c331 := derived331 a h
  have h3 : Entails.eval a c256 := derived256 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c344 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f344 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c342, some c335, some c285, some c12, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p344 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked344 : lratChecker f344 p344 = .success := by decide +kernel
theorem unsat344 : Unsatisfiable (PosFin 31) f344 := by
  apply lratCheckerSound f344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p344
  · intro a ha; simp [p344] at ha; subst a; trivial
  · exact checked344
theorem derived344 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c344 := by
  apply localUnsat_implies_entails f344 [c342, c335, c285, c12] c344 unsat344 (by rfl) a
  have h0 : Entails.eval a c342 := derived342 a h
  have h1 : Entails.eval a c335 := derived335 a h
  have h2 : Entails.eval a c285 := derived285 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c345 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f345 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c343, some c339, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p345 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked345 : lratChecker f345 p345 = .success := by decide +kernel
theorem unsat345 : Unsatisfiable (PosFin 31) f345 := by
  apply lratCheckerSound f345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p345
  · intro a ha; simp [p345] at ha; subst a; trivial
  · exact checked345
theorem derived345 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c345 := by
  apply localUnsat_implies_entails f345 [c343, c339] c345 unsat345 (by rfl) a
  have h0 : Entails.eval a c343 := derived343 a h
  have h1 : Entails.eval a c339 := derived339 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c346 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f346 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c344, some c345, some c331, some c341, some c180]
def p346 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked346 : lratChecker f346 p346 = .success := by decide +kernel
theorem unsat346 : Unsatisfiable (PosFin 31) f346 := by
  apply lratCheckerSound f346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p346
  · intro a ha; simp [p346] at ha; subst a; trivial
  · exact checked346
theorem derived346 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c346 := by
  apply localUnsat_implies_entails f346 [c344, c345, c331, c341, c180] c346 unsat346 (by rfl) a
  have h0 : Entails.eval a c344 := derived344 a h
  have h1 : Entails.eval a c345 := derived345 a h
  have h2 : Entails.eval a c331 := derived331 a h
  have h3 : Entails.eval a c341 := derived341 a h
  have h4 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived346

end CochromaticTwenty.Certificates.Z12Direct_5_8_1
