import MerLeanExperiment.Certificates.Z12Direct_5_3_1.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_3_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c299 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f299 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c298, some c296, some c290, some c114, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p299 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked299 : lratChecker f299 p299 = .success := by decide +kernel
theorem unsat299 : Unsatisfiable (PosFin 31) f299 := by
  apply lratCheckerSound f299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p299
  · intro a ha; simp [p299] at ha; subst a; trivial
  · exact checked299
theorem derived299 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c299 := by
  apply localUnsat_implies_entails f299 [c298, c296, c290, c114] c299 unsat299 (by rfl) a
  have h0 : Entails.eval a c298 := derived298 a h
  have h1 : Entails.eval a c296 := derived296 a h
  have h2 : Entails.eval a c290 := derived290 a h
  have h3 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c300 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f300 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c298, some c296, some c290, some c74, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p300 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked300 : lratChecker f300 p300 = .success := by decide +kernel
theorem unsat300 : Unsatisfiable (PosFin 31) f300 := by
  apply lratCheckerSound f300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p300
  · intro a ha; simp [p300] at ha; subst a; trivial
  · exact checked300
theorem derived300 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c300 := by
  apply localUnsat_implies_entails f300 [c298, c296, c290, c74] c300 unsat300 (by rfl) a
  have h0 : Entails.eval a c298 := derived298 a h
  have h1 : Entails.eval a c296 := derived296 a h
  have h2 : Entails.eval a c290 := derived290 a h
  have h3 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c301 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f301 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c299, some c284, some c290, some c45, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p301 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked301 : lratChecker f301 p301 = .success := by decide +kernel
theorem unsat301 : Unsatisfiable (PosFin 31) f301 := by
  apply lratCheckerSound f301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p301
  · intro a ha; simp [p301] at ha; subst a; trivial
  · exact checked301
theorem derived301 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c301 := by
  apply localUnsat_implies_entails f301 [c299, c284, c290, c45] c301 unsat301 (by rfl) a
  have h0 : Entails.eval a c299 := derived299 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c290 := derived290 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c302 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f302 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c299, some c284, some c18, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p302 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked302 : lratChecker f302 p302 = .success := by decide +kernel
theorem unsat302 : Unsatisfiable (PosFin 31) f302 := by
  apply lratCheckerSound f302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p302
  · intro a ha; simp [p302] at ha; subst a; trivial
  · exact checked302
theorem derived302 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c302 := by
  apply localUnsat_implies_entails f302 [c299, c284, c18] c302 unsat302 (by rfl) a
  have h0 : Entails.eval a c299 := derived299 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c303 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f303 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c301, some c264, some c291, some c33, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p303 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked303 : lratChecker f303 p303 = .success := by decide +kernel
theorem unsat303 : Unsatisfiable (PosFin 31) f303 := by
  apply lratCheckerSound f303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p303
  · intro a ha; simp [p303] at ha; subst a; trivial
  · exact checked303
theorem derived303 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c303 := by
  apply localUnsat_implies_entails f303 [c301, c264, c291, c33] c303 unsat303 (by rfl) a
  have h0 : Entails.eval a c301 := derived301 a h
  have h1 : Entails.eval a c264 := derived264 a h
  have h2 : Entails.eval a c291 := derived291 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c304 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f304 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c301, some c296, some c284, some c38, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p304 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked304 : lratChecker f304 p304 = .success := by decide +kernel
theorem unsat304 : Unsatisfiable (PosFin 31) f304 := by
  apply lratCheckerSound f304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p304
  · intro a ha; simp [p304] at ha; subst a; trivial
  · exact checked304
theorem derived304 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c304 := by
  apply localUnsat_implies_entails f304 [c301, c296, c284, c38] c304 unsat304 (by rfl) a
  have h0 : Entails.eval a c301 := derived301 a h
  have h1 : Entails.eval a c296 := derived296 a h
  have h2 : Entails.eval a c284 := derived284 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c305 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f305 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c302, some c291, some c301, some c12, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p305 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked305 : lratChecker f305 p305 = .success := by decide +kernel
theorem unsat305 : Unsatisfiable (PosFin 31) f305 := by
  apply lratCheckerSound f305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p305
  · intro a ha; simp [p305] at ha; subst a; trivial
  · exact checked305
theorem derived305 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c305 := by
  apply localUnsat_implies_entails f305 [c302, c291, c301, c12] c305 unsat305 (by rfl) a
  have h0 : Entails.eval a c302 := derived302 a h
  have h1 : Entails.eval a c291 := derived291 a h
  have h2 : Entails.eval a c301 := derived301 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c306 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f306 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c303, some c194, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p306 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked306 : lratChecker f306 p306 = .success := by decide +kernel
theorem unsat306 : Unsatisfiable (PosFin 31) f306 := by
  apply lratCheckerSound f306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p306
  · intro a ha; simp [p306] at ha; subst a; trivial
  · exact checked306
theorem derived306 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c306 := by
  apply localUnsat_implies_entails f306 [c303, c194] c306 unsat306 (by rfl) a
  have h0 : Entails.eval a c303 := derived303 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c307 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f307 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c304, some c297, some c264, some c88, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p307 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked307 : lratChecker f307 p307 = .success := by decide +kernel
theorem unsat307 : Unsatisfiable (PosFin 31) f307 := by
  apply lratCheckerSound f307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p307
  · intro a ha; simp [p307] at ha; subst a; trivial
  · exact checked307
theorem derived307 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c307 := by
  apply localUnsat_implies_entails f307 [c304, c297, c264, c88] c307 unsat307 (by rfl) a
  have h0 : Entails.eval a c304 := derived304 a h
  have h1 : Entails.eval a c297 := derived297 a h
  have h2 : Entails.eval a c264 := derived264 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c308 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f308 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c304, some c284, some c306, some c299, some c264, some c150, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p308 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked308 : lratChecker f308 p308 = .success := by decide +kernel
theorem unsat308 : Unsatisfiable (PosFin 31) f308 := by
  apply lratCheckerSound f308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p308
  · intro a ha; simp [p308] at ha; subst a; trivial
  · exact checked308
theorem derived308 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c308 := by
  apply localUnsat_implies_entails f308 [c304, c284, c306, c299, c264, c150] c308 unsat308 (by rfl) a
  have h0 : Entails.eval a c304 := derived304 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c306 := derived306 a h
  have h3 : Entails.eval a c299 := derived299 a h
  have h4 : Entails.eval a c264 := derived264 a h
  have h5 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c309 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f309 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c305, some c308, some c300, some c307, some c289, some c263, some c68]
def p309 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked309 : lratChecker f309 p309 = .success := by decide +kernel
theorem unsat309 : Unsatisfiable (PosFin 31) f309 := by
  apply lratCheckerSound f309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p309
  · intro a ha; simp [p309] at ha; subst a; trivial
  · exact checked309
theorem derived309 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c309 := by
  apply localUnsat_implies_entails f309 [c305, c308, c300, c307, c289, c263, c68] c309 unsat309 (by rfl) a
  have h0 : Entails.eval a c305 := derived305 a h
  have h1 : Entails.eval a c308 := derived308 a h
  have h2 : Entails.eval a c300 := derived300 a h
  have h3 : Entails.eval a c307 := derived307 a h
  have h4 : Entails.eval a c289 := derived289 a h
  have h5 : Entails.eval a c263 := derived263 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived309

end CochromaticTwenty.Certificates.Z12Direct_5_3_1
