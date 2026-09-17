import MerLeanExperiment.Certificates.FixedCore0.Steps2600_2699

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10251 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10251 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1565, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10251 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10251 : lratChecker f10251 p10251 = .success := by decide +kernel
theorem unsat10251 : Unsatisfiable (PosFin 65) f10251 := by
  apply lratCheckerSound f10251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10251
  · intro a ha; simp [p10251] at ha; subst a; trivial
  · exact checked10251
theorem derived10251 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10251 := by
  apply localUnsat_implies_entails f10251 [c9748, c1565] c10251 unsat10251 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1565 := h 1564 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10252 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10252 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1570, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p10252 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10252 : lratChecker f10252 p10252 = .success := by decide +kernel
theorem unsat10252 : Unsatisfiable (PosFin 65) f10252 := by
  apply lratCheckerSound f10252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10252
  · intro a ha; simp [p10252] at ha; subst a; trivial
  · exact checked10252
theorem derived10252 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10252 := by
  apply localUnsat_implies_entails f10252 [c9748, c1570] c10252 unsat10252 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1570 := h 1569 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10253 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨7, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10253 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1508, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p10253 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10253 : lratChecker f10253 p10253 = .success := by decide +kernel
theorem unsat10253 : Unsatisfiable (PosFin 65) f10253 := by
  apply lratCheckerSound f10253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10253
  · intro a ha; simp [p10253] at ha; subst a; trivial
  · exact checked10253
theorem derived10253 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10253 := by
  apply localUnsat_implies_entails f10253 [c9748, c1508] c10253 unsat10253 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1508 := h 1507 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10254 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨58, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10254 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1576, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10254 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10254 : lratChecker f10254 p10254 = .success := by decide +kernel
theorem unsat10254 : Unsatisfiable (PosFin 65) f10254 := by
  apply lratCheckerSound f10254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10254
  · intro a ha; simp [p10254] at ha; subst a; trivial
  · exact checked10254
theorem derived10254 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10254 := by
  apply localUnsat_implies_entails f10254 [c9748, c1576] c10254 unsat10254 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1576 := h 1575 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10255 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10255 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1455, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10255 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10255 : lratChecker f10255 p10255 = .success := by decide +kernel
theorem unsat10255 : Unsatisfiable (PosFin 65) f10255 := by
  apply lratCheckerSound f10255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10255
  · intro a ha; simp [p10255] at ha; subst a; trivial
  · exact checked10255
theorem derived10255 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10255 := by
  apply localUnsat_implies_entails f10255 [c9748, c1455] c10255 unsat10255 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1455 := h 1454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10256 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10256 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1497, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10256 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10256 : lratChecker f10256 p10256 = .success := by decide +kernel
theorem unsat10256 : Unsatisfiable (PosFin 65) f10256 := by
  apply lratCheckerSound f10256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10256
  · intro a ha; simp [p10256] at ha; subst a; trivial
  · exact checked10256
theorem derived10256 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10256 := by
  apply localUnsat_implies_entails f10256 [c9748, c1497] c10256 unsat10256 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1497 := h 1496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10257 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10257 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1578, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10257 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10257 : lratChecker f10257 p10257 = .success := by decide +kernel
theorem unsat10257 : Unsatisfiable (PosFin 65) f10257 := by
  apply lratCheckerSound f10257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10257
  · intro a ha; simp [p10257] at ha; subst a; trivial
  · exact checked10257
theorem derived10257 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10257 := by
  apply localUnsat_implies_entails f10257 [c9748, c1578] c10257 unsat10257 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1578 := h 1577 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10258 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨20, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10258 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1538, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10258 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10258 : lratChecker f10258 p10258 = .success := by decide +kernel
theorem unsat10258 : Unsatisfiable (PosFin 65) f10258 := by
  apply lratCheckerSound f10258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10258
  · intro a ha; simp [p10258] at ha; subst a; trivial
  · exact checked10258
theorem derived10258 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10258 := by
  apply localUnsat_implies_entails f10258 [c9748, c1538] c10258 unsat10258 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1538 := h 1537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10259 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10259 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1547, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10259 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10259 : lratChecker f10259 p10259 = .success := by decide +kernel
theorem unsat10259 : Unsatisfiable (PosFin 65) f10259 := by
  apply lratCheckerSound f10259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10259
  · intro a ha; simp [p10259] at ha; subst a; trivial
  · exact checked10259
theorem derived10259 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10259 := by
  apply localUnsat_implies_entails f10259 [c9748, c1547] c10259 unsat10259 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1547 := h 1546 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10260 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨59, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10260 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1569, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10260 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10260 : lratChecker f10260 p10260 = .success := by decide +kernel
theorem unsat10260 : Unsatisfiable (PosFin 65) f10260 := by
  apply lratCheckerSound f10260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10260
  · intro a ha; simp [p10260] at ha; subst a; trivial
  · exact checked10260
theorem derived10260 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10260 := by
  apply localUnsat_implies_entails f10260 [c9748, c1569] c10260 unsat10260 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1569 := h 1568 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10261 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨5, by decide⟩, true), (⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10261 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1588, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10261 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10261 : lratChecker f10261 p10261 = .success := by decide +kernel
theorem unsat10261 : Unsatisfiable (PosFin 65) f10261 := by
  apply lratCheckerSound f10261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10261
  · intro a ha; simp [p10261] at ha; subst a; trivial
  · exact checked10261
theorem derived10261 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10261 := by
  apply localUnsat_implies_entails f10261 [c9748, c1588] c10261 unsat10261 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1588 := h 1587 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10262 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10262 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1561, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10262 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10262 : lratChecker f10262 p10262 = .success := by decide +kernel
theorem unsat10262 : Unsatisfiable (PosFin 65) f10262 := by
  apply lratCheckerSound f10262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10262
  · intro a ha; simp [p10262] at ha; subst a; trivial
  · exact checked10262
theorem derived10262 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10262 := by
  apply localUnsat_implies_entails f10262 [c9748, c1561] c10262 unsat10262 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1561 := h 1560 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10263 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨50, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10263 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1562, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10263 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10263 : lratChecker f10263 p10263 = .success := by decide +kernel
theorem unsat10263 : Unsatisfiable (PosFin 65) f10263 := by
  apply lratCheckerSound f10263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10263
  · intro a ha; simp [p10263] at ha; subst a; trivial
  · exact checked10263
theorem derived10263 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10263 := by
  apply localUnsat_implies_entails f10263 [c9748, c1562] c10263 unsat10263 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1562 := h 1561 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10264 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨35, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10264 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1537, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p10264 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10264 : lratChecker f10264 p10264 = .success := by decide +kernel
theorem unsat10264 : Unsatisfiable (PosFin 65) f10264 := by
  apply lratCheckerSound f10264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10264
  · intro a ha; simp [p10264] at ha; subst a; trivial
  · exact checked10264
theorem derived10264 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10264 := by
  apply localUnsat_implies_entails f10264 [c9748, c1537] c10264 unsat10264 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1537 := h 1536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10265 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨58, by decide⟩, false), (⟨15, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10265 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1590, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10265 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10265 : lratChecker f10265 p10265 = .success := by decide +kernel
theorem unsat10265 : Unsatisfiable (PosFin 65) f10265 := by
  apply lratCheckerSound f10265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10265
  · intro a ha; simp [p10265] at ha; subst a; trivial
  · exact checked10265
theorem derived10265 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10265 := by
  apply localUnsat_implies_entails f10265 [c9748, c1590] c10265 unsat10265 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1590 := h 1589 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10266 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10266 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1550, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10266 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10266 : lratChecker f10266 p10266 = .success := by decide +kernel
theorem unsat10266 : Unsatisfiable (PosFin 65) f10266 := by
  apply lratCheckerSound f10266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10266
  · intro a ha; simp [p10266] at ha; subst a; trivial
  · exact checked10266
theorem derived10266 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10266 := by
  apply localUnsat_implies_entails f10266 [c9748, c1550] c10266 unsat10266 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1550 := h 1549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10267 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10267 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1544, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10267 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10267 : lratChecker f10267 p10267 = .success := by decide +kernel
theorem unsat10267 : Unsatisfiable (PosFin 65) f10267 := by
  apply lratCheckerSound f10267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10267
  · intro a ha; simp [p10267] at ha; subst a; trivial
  · exact checked10267
theorem derived10267 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10267 := by
  apply localUnsat_implies_entails f10267 [c9748, c1544] c10267 unsat10267 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1544 := h 1543 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10268 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10268 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1545, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10268 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10268 : lratChecker f10268 p10268 = .success := by decide +kernel
theorem unsat10268 : Unsatisfiable (PosFin 65) f10268 := by
  apply lratCheckerSound f10268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10268
  · intro a ha; simp [p10268] at ha; subst a; trivial
  · exact checked10268
theorem derived10268 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10268 := by
  apply localUnsat_implies_entails f10268 [c9748, c1545] c10268 unsat10268 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1545 := h 1544 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10269 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨51, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10269 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1574, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10269 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10269 : lratChecker f10269 p10269 = .success := by decide +kernel
theorem unsat10269 : Unsatisfiable (PosFin 65) f10269 := by
  apply lratCheckerSound f10269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10269
  · intro a ha; simp [p10269] at ha; subst a; trivial
  · exact checked10269
theorem derived10269 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10269 := by
  apply localUnsat_implies_entails f10269 [c9748, c1574] c10269 unsat10269 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1574 := h 1573 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10270 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10270 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1543, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10270 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10270 : lratChecker f10270 p10270 = .success := by decide +kernel
theorem unsat10270 : Unsatisfiable (PosFin 65) f10270 := by
  apply lratCheckerSound f10270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10270
  · intro a ha; simp [p10270] at ha; subst a; trivial
  · exact checked10270
theorem derived10270 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10270 := by
  apply localUnsat_implies_entails f10270 [c9748, c1543] c10270 unsat10270 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1543 := h 1542 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10271 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10271 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1571, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10271 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10271 : lratChecker f10271 p10271 = .success := by decide +kernel
theorem unsat10271 : Unsatisfiable (PosFin 65) f10271 := by
  apply lratCheckerSound f10271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10271
  · intro a ha; simp [p10271] at ha; subst a; trivial
  · exact checked10271
theorem derived10271 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10271 := by
  apply localUnsat_implies_entails f10271 [c9748, c1571] c10271 unsat10271 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1571 := h 1570 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10272 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10272 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1573, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10272 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10272 : lratChecker f10272 p10272 = .success := by decide +kernel
theorem unsat10272 : Unsatisfiable (PosFin 65) f10272 := by
  apply lratCheckerSound f10272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10272
  · intro a ha; simp [p10272] at ha; subst a; trivial
  · exact checked10272
theorem derived10272 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10272 := by
  apply localUnsat_implies_entails f10272 [c9748, c1573] c10272 unsat10272 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1573 := h 1572 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10273 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10273 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1539, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10273 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10273 : lratChecker f10273 p10273 = .success := by decide +kernel
theorem unsat10273 : Unsatisfiable (PosFin 65) f10273 := by
  apply lratCheckerSound f10273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10273
  · intro a ha; simp [p10273] at ha; subst a; trivial
  · exact checked10273
theorem derived10273 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10273 := by
  apply localUnsat_implies_entails f10273 [c9748, c1539] c10273 unsat10273 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1539 := h 1538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10274 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10274 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1541, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10274 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10274 : lratChecker f10274 p10274 = .success := by decide +kernel
theorem unsat10274 : Unsatisfiable (PosFin 65) f10274 := by
  apply lratCheckerSound f10274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10274
  · intro a ha; simp [p10274] at ha; subst a; trivial
  · exact checked10274
theorem derived10274 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10274 := by
  apply localUnsat_implies_entails f10274 [c9748, c1541] c10274 unsat10274 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1541 := h 1540 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10275 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10275 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1546, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10275 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10275 : lratChecker f10275 p10275 = .success := by decide +kernel
theorem unsat10275 : Unsatisfiable (PosFin 65) f10275 := by
  apply lratCheckerSound f10275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10275
  · intro a ha; simp [p10275] at ha; subst a; trivial
  · exact checked10275
theorem derived10275 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10275 := by
  apply localUnsat_implies_entails f10275 [c9748, c1546] c10275 unsat10275 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1546 := h 1545 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10276 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10276 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1585, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10276 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10276 : lratChecker f10276 p10276 = .success := by decide +kernel
theorem unsat10276 : Unsatisfiable (PosFin 65) f10276 := by
  apply lratCheckerSound f10276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10276
  · intro a ha; simp [p10276] at ha; subst a; trivial
  · exact checked10276
theorem derived10276 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10276 := by
  apply localUnsat_implies_entails f10276 [c9748, c1585] c10276 unsat10276 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1585 := h 1584 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10277 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10277 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1572, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10277 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10277 : lratChecker f10277 p10277 = .success := by decide +kernel
theorem unsat10277 : Unsatisfiable (PosFin 65) f10277 := by
  apply lratCheckerSound f10277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10277
  · intro a ha; simp [p10277] at ha; subst a; trivial
  · exact checked10277
theorem derived10277 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10277 := by
  apply localUnsat_implies_entails f10277 [c9748, c1572] c10277 unsat10277 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1572 := h 1571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10278 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨60, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10278 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1566, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10278 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10278 : lratChecker f10278 p10278 = .success := by decide +kernel
theorem unsat10278 : Unsatisfiable (PosFin 65) f10278 := by
  apply lratCheckerSound f10278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10278
  · intro a ha; simp [p10278] at ha; subst a; trivial
  · exact checked10278
theorem derived10278 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10278 := by
  apply localUnsat_implies_entails f10278 [c9748, c1566] c10278 unsat10278 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1566 := h 1565 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10279 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10279 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1563, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10279 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10279 : lratChecker f10279 p10279 = .success := by decide +kernel
theorem unsat10279 : Unsatisfiable (PosFin 65) f10279 := by
  apply lratCheckerSound f10279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10279
  · intro a ha; simp [p10279] at ha; subst a; trivial
  · exact checked10279
theorem derived10279 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10279 := by
  apply localUnsat_implies_entails f10279 [c9748, c1563] c10279 unsat10279 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1563 := h 1562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10280 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10280 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1568, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10280 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10280 : lratChecker f10280 p10280 = .success := by decide +kernel
theorem unsat10280 : Unsatisfiable (PosFin 65) f10280 := by
  apply lratCheckerSound f10280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10280
  · intro a ha; simp [p10280] at ha; subst a; trivial
  · exact checked10280
theorem derived10280 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10280 := by
  apply localUnsat_implies_entails f10280 [c9748, c1568] c10280 unsat10280 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1568 := h 1567 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10281 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨38, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10281 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1488, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10281 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10281 : lratChecker f10281 p10281 = .success := by decide +kernel
theorem unsat10281 : Unsatisfiable (PosFin 65) f10281 := by
  apply lratCheckerSound f10281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10281
  · intro a ha; simp [p10281] at ha; subst a; trivial
  · exact checked10281
theorem derived10281 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10281 := by
  apply localUnsat_implies_entails f10281 [c9748, c1488] c10281 unsat10281 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1488 := h 1487 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10282 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10282 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1642, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p10282 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10282 : lratChecker f10282 p10282 = .success := by decide +kernel
theorem unsat10282 : Unsatisfiable (PosFin 65) f10282 := by
  apply lratCheckerSound f10282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10282
  · intro a ha; simp [p10282] at ha; subst a; trivial
  · exact checked10282
theorem derived10282 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10282 := by
  apply localUnsat_implies_entails f10282 [c9748, c1642] c10282 unsat10282 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1642 := h 1641 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10283 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10283 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1645, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10283 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10283 : lratChecker f10283 p10283 = .success := by decide +kernel
theorem unsat10283 : Unsatisfiable (PosFin 65) f10283 := by
  apply lratCheckerSound f10283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10283
  · intro a ha; simp [p10283] at ha; subst a; trivial
  · exact checked10283
theorem derived10283 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10283 := by
  apply localUnsat_implies_entails f10283 [c9748, c1645] c10283 unsat10283 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1645 := h 1644 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10284 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10284 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2029, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10284 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10284 : lratChecker f10284 p10284 = .success := by decide +kernel
theorem unsat10284 : Unsatisfiable (PosFin 65) f10284 := by
  apply lratCheckerSound f10284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10284
  · intro a ha; simp [p10284] at ha; subst a; trivial
  · exact checked10284
theorem derived10284 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10284 := by
  apply localUnsat_implies_entails f10284 [c9748, c2029] c10284 unsat10284 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2029 := h 2028 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10285 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨51, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10285 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2012, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10285 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10285 : lratChecker f10285 p10285 = .success := by decide +kernel
theorem unsat10285 : Unsatisfiable (PosFin 65) f10285 := by
  apply lratCheckerSound f10285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10285
  · intro a ha; simp [p10285] at ha; subst a; trivial
  · exact checked10285
theorem derived10285 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10285 := by
  apply localUnsat_implies_entails f10285 [c9748, c2012] c10285 unsat10285 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2012 := h 2011 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10286 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨51, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10286 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2010, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10286 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10286 : lratChecker f10286 p10286 = .success := by decide +kernel
theorem unsat10286 : Unsatisfiable (PosFin 65) f10286 := by
  apply lratCheckerSound f10286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10286
  · intro a ha; simp [p10286] at ha; subst a; trivial
  · exact checked10286
theorem derived10286 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10286 := by
  apply localUnsat_implies_entails f10286 [c9748, c2010] c10286 unsat10286 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2010 := h 2009 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10287 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨13, by decide⟩, true), (⟨50, by decide⟩, false), (⟨60, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10287 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2006, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10287 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10287 : lratChecker f10287 p10287 = .success := by decide +kernel
theorem unsat10287 : Unsatisfiable (PosFin 65) f10287 := by
  apply lratCheckerSound f10287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10287
  · intro a ha; simp [p10287] at ha; subst a; trivial
  · exact checked10287
theorem derived10287 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10287 := by
  apply localUnsat_implies_entails f10287 [c9748, c2006] c10287 unsat10287 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2006 := h 2005 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10288 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨13, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10288 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2008, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p10288 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10288 : lratChecker f10288 p10288 = .success := by decide +kernel
theorem unsat10288 : Unsatisfiable (PosFin 65) f10288 := by
  apply lratCheckerSound f10288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10288
  · intro a ha; simp [p10288] at ha; subst a; trivial
  · exact checked10288
theorem derived10288 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10288 := by
  apply localUnsat_implies_entails f10288 [c9748, c2008] c10288 unsat10288 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2008 := h 2007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10289 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨51, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10289 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2248, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10289 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10289 : lratChecker f10289 p10289 = .success := by decide +kernel
theorem unsat10289 : Unsatisfiable (PosFin 65) f10289 := by
  apply lratCheckerSound f10289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10289
  · intro a ha; simp [p10289] at ha; subst a; trivial
  · exact checked10289
theorem derived10289 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10289 := by
  apply localUnsat_implies_entails f10289 [c9748, c2248] c10289 unsat10289 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2248 := h 2247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10290 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10290 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2259, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10290 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10290 : lratChecker f10290 p10290 = .success := by decide +kernel
theorem unsat10290 : Unsatisfiable (PosFin 65) f10290 := by
  apply lratCheckerSound f10290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10290
  · intro a ha; simp [p10290] at ha; subst a; trivial
  · exact checked10290
theorem derived10290 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10290 := by
  apply localUnsat_implies_entails f10290 [c9748, c2259] c10290 unsat10290 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2259 := h 2258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10291 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨51, by decide⟩, true), (⟨13, by decide⟩, true), (⟨54, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10291 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2244, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10291 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10291 : lratChecker f10291 p10291 = .success := by decide +kernel
theorem unsat10291 : Unsatisfiable (PosFin 65) f10291 := by
  apply lratCheckerSound f10291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10291
  · intro a ha; simp [p10291] at ha; subst a; trivial
  · exact checked10291
theorem derived10291 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10291 := by
  apply localUnsat_implies_entails f10291 [c9748, c2244] c10291 unsat10291 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2244 := h 2243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10292 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨13, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10292 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2240, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10292 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10292 : lratChecker f10292 p10292 = .success := by decide +kernel
theorem unsat10292 : Unsatisfiable (PosFin 65) f10292 := by
  apply lratCheckerSound f10292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10292
  · intro a ha; simp [p10292] at ha; subst a; trivial
  · exact checked10292
theorem derived10292 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10292 := by
  apply localUnsat_implies_entails f10292 [c9748, c2240] c10292 unsat10292 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2240 := h 2239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10293 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨56, by decide⟩, false), (⟨13, by decide⟩, true), (⟨50, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10293 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2239, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10293 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10293 : lratChecker f10293 p10293 = .success := by decide +kernel
theorem unsat10293 : Unsatisfiable (PosFin 65) f10293 := by
  apply lratCheckerSound f10293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10293
  · intro a ha; simp [p10293] at ha; subst a; trivial
  · exact checked10293
theorem derived10293 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10293 := by
  apply localUnsat_implies_entails f10293 [c9748, c2239] c10293 unsat10293 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2239 := h 2238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10294 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10294 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2023, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10294 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10294 : lratChecker f10294 p10294 = .success := by decide +kernel
theorem unsat10294 : Unsatisfiable (PosFin 65) f10294 := by
  apply lratCheckerSound f10294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10294
  · intro a ha; simp [p10294] at ha; subst a; trivial
  · exact checked10294
theorem derived10294 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10294 := by
  apply localUnsat_implies_entails f10294 [c9748, c2023] c10294 unsat10294 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2023 := h 2022 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10295 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10295 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2024, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10295 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10295 : lratChecker f10295 p10295 = .success := by decide +kernel
theorem unsat10295 : Unsatisfiable (PosFin 65) f10295 := by
  apply lratCheckerSound f10295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10295
  · intro a ha; simp [p10295] at ha; subst a; trivial
  · exact checked10295
theorem derived10295 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10295 := by
  apply localUnsat_implies_entails f10295 [c9748, c2024] c10295 unsat10295 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2024 := h 2023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10296 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10296 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1998, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10296 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10296 : lratChecker f10296 p10296 = .success := by decide +kernel
theorem unsat10296 : Unsatisfiable (PosFin 65) f10296 := by
  apply lratCheckerSound f10296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10296
  · intro a ha; simp [p10296] at ha; subst a; trivial
  · exact checked10296
theorem derived10296 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10296 := by
  apply localUnsat_implies_entails f10296 [c9748, c1998] c10296 unsat10296 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1998 := h 1997 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10297 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨13, by decide⟩, true), (⟨53, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10297 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2009, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10297 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10297 : lratChecker f10297 p10297 = .success := by decide +kernel
theorem unsat10297 : Unsatisfiable (PosFin 65) f10297 := by
  apply lratCheckerSound f10297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10297
  · intro a ha; simp [p10297] at ha; subst a; trivial
  · exact checked10297
theorem derived10297 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10297 := by
  apply localUnsat_implies_entails f10297 [c9748, c2009] c10297 unsat10297 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2009 := h 2008 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10298 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10298 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2025, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10298 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10298 : lratChecker f10298 p10298 = .success := by decide +kernel
theorem unsat10298 : Unsatisfiable (PosFin 65) f10298 := by
  apply lratCheckerSound f10298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10298
  · intro a ha; simp [p10298] at ha; subst a; trivial
  · exact checked10298
theorem derived10298 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10298 := by
  apply localUnsat_implies_entails f10298 [c9748, c2025] c10298 unsat10298 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2025 := h 2024 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10299 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10299 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2016, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10299 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10299 : lratChecker f10299 p10299 = .success := by decide +kernel
theorem unsat10299 : Unsatisfiable (PosFin 65) f10299 := by
  apply lratCheckerSound f10299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10299
  · intro a ha; simp [p10299] at ha; subst a; trivial
  · exact checked10299
theorem derived10299 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10299 := by
  apply localUnsat_implies_entails f10299 [c9748, c2016] c10299 unsat10299 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2016 := h 2015 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10300 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10300 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2028, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10300 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10300 : lratChecker f10300 p10300 = .success := by decide +kernel
theorem unsat10300 : Unsatisfiable (PosFin 65) f10300 := by
  apply lratCheckerSound f10300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10300
  · intro a ha; simp [p10300] at ha; subst a; trivial
  · exact checked10300
theorem derived10300 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10300 := by
  apply localUnsat_implies_entails f10300 [c9748, c2028] c10300 unsat10300 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2028 := h 2027 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10301 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10301 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2002, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10301 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10301 : lratChecker f10301 p10301 = .success := by decide +kernel
theorem unsat10301 : Unsatisfiable (PosFin 65) f10301 := by
  apply lratCheckerSound f10301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10301
  · intro a ha; simp [p10301] at ha; subst a; trivial
  · exact checked10301
theorem derived10301 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10301 := by
  apply localUnsat_implies_entails f10301 [c9748, c2002] c10301 unsat10301 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2002 := h 2001 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10302 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨13, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10302 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2022, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10302 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10302 : lratChecker f10302 p10302 = .success := by decide +kernel
theorem unsat10302 : Unsatisfiable (PosFin 65) f10302 := by
  apply lratCheckerSound f10302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10302
  · intro a ha; simp [p10302] at ha; subst a; trivial
  · exact checked10302
theorem derived10302 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10302 := by
  apply localUnsat_implies_entails f10302 [c9748, c2022] c10302 unsat10302 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2022 := h 2021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10303 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10303 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2328, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10303 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10303 : lratChecker f10303 p10303 = .success := by decide +kernel
theorem unsat10303 : Unsatisfiable (PosFin 65) f10303 := by
  apply lratCheckerSound f10303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10303
  · intro a ha; simp [p10303] at ha; subst a; trivial
  · exact checked10303
theorem derived10303 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10303 := by
  apply localUnsat_implies_entails f10303 [c9748, c2328] c10303 unsat10303 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2328 := h 2327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10304 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨56, by decide⟩, false), (⟨13, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10304 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2021, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10304 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10304 : lratChecker f10304 p10304 = .success := by decide +kernel
theorem unsat10304 : Unsatisfiable (PosFin 65) f10304 := by
  apply lratCheckerSound f10304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10304
  · intro a ha; simp [p10304] at ha; subst a; trivial
  · exact checked10304
theorem derived10304 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10304 := by
  apply localUnsat_implies_entails f10304 [c9748, c2021] c10304 unsat10304 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2021 := h 2020 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10305 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨62, by decide⟩, false), (⟨7, by decide⟩, true), (⟨60, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10305 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2033, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10305 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10305 : lratChecker f10305 p10305 = .success := by decide +kernel
theorem unsat10305 : Unsatisfiable (PosFin 65) f10305 := by
  apply lratCheckerSound f10305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10305
  · intro a ha; simp [p10305] at ha; subst a; trivial
  · exact checked10305
theorem derived10305 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10305 := by
  apply localUnsat_implies_entails f10305 [c9748, c2033] c10305 unsat10305 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2033 := h 2032 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10306 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨58, by decide⟩, true), (⟨13, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10306 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2241, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p10306 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10306 : lratChecker f10306 p10306 = .success := by decide +kernel
theorem unsat10306 : Unsatisfiable (PosFin 65) f10306 := by
  apply lratCheckerSound f10306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10306
  · intro a ha; simp [p10306] at ha; subst a; trivial
  · exact checked10306
theorem derived10306 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10306 := by
  apply localUnsat_implies_entails f10306 [c9748, c2241] c10306 unsat10306 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2241 := h 2240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10307 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨13, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10307 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2257, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10307 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10307 : lratChecker f10307 p10307 = .success := by decide +kernel
theorem unsat10307 : Unsatisfiable (PosFin 65) f10307 := by
  apply lratCheckerSound f10307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10307
  · intro a ha; simp [p10307] at ha; subst a; trivial
  · exact checked10307
theorem derived10307 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10307 := by
  apply localUnsat_implies_entails f10307 [c9748, c2257] c10307 unsat10307 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2257 := h 2256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10308 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, true), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10308 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2329, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10308 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10308 : lratChecker f10308 p10308 = .success := by decide +kernel
theorem unsat10308 : Unsatisfiable (PosFin 65) f10308 := by
  apply lratCheckerSound f10308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10308
  · intro a ha; simp [p10308] at ha; subst a; trivial
  · exact checked10308
theorem derived10308 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10308 := by
  apply localUnsat_implies_entails f10308 [c9748, c2329] c10308 unsat10308 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2329 := h 2328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10309 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10309 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2250, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10309 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10309 : lratChecker f10309 p10309 = .success := by decide +kernel
theorem unsat10309 : Unsatisfiable (PosFin 65) f10309 := by
  apply lratCheckerSound f10309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10309
  · intro a ha; simp [p10309] at ha; subst a; trivial
  · exact checked10309
theorem derived10309 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10309 := by
  apply localUnsat_implies_entails f10309 [c9748, c2250] c10309 unsat10309 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2250 := h 2249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10310 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10310 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2235, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p10310 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10310 : lratChecker f10310 p10310 = .success := by decide +kernel
theorem unsat10310 : Unsatisfiable (PosFin 65) f10310 := by
  apply lratCheckerSound f10310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10310
  · intro a ha; simp [p10310] at ha; subst a; trivial
  · exact checked10310
theorem derived10310 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10310 := by
  apply localUnsat_implies_entails f10310 [c9748, c2235] c10310 unsat10310 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2235 := h 2234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10311 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨16, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10311 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2326, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10311 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10311 : lratChecker f10311 p10311 = .success := by decide +kernel
theorem unsat10311 : Unsatisfiable (PosFin 65) f10311 := by
  apply lratCheckerSound f10311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10311
  · intro a ha; simp [p10311] at ha; subst a; trivial
  · exact checked10311
theorem derived10311 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10311 := by
  apply localUnsat_implies_entails f10311 [c9748, c2326] c10311 unsat10311 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2326 := h 2325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10312 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨14, by decide⟩, true), (⟨57, by decide⟩, true), (⟨63, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10312 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2254, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10312 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10312 : lratChecker f10312 p10312 = .success := by decide +kernel
theorem unsat10312 : Unsatisfiable (PosFin 65) f10312 := by
  apply lratCheckerSound f10312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10312
  · intro a ha; simp [p10312] at ha; subst a; trivial
  · exact checked10312
theorem derived10312 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10312 := by
  apply localUnsat_implies_entails f10312 [c9748, c2254] c10312 unsat10312 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2254 := h 2253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10313 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨51, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10313 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2234, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10313 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10313 : lratChecker f10313 p10313 = .success := by decide +kernel
theorem unsat10313 : Unsatisfiable (PosFin 65) f10313 := by
  apply lratCheckerSound f10313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10313
  · intro a ha; simp [p10313] at ha; subst a; trivial
  · exact checked10313
theorem derived10313 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10313 := by
  apply localUnsat_implies_entails f10313 [c9748, c2234] c10313 unsat10313 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2234 := h 2233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10314 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨13, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10314 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2252, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p10314 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10314 : lratChecker f10314 p10314 = .success := by decide +kernel
theorem unsat10314 : Unsatisfiable (PosFin 65) f10314 := by
  apply lratCheckerSound f10314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10314
  · intro a ha; simp [p10314] at ha; subst a; trivial
  · exact checked10314
theorem derived10314 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10314 := by
  apply localUnsat_implies_entails f10314 [c9748, c2252] c10314 unsat10314 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2252 := h 2251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10315 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10315 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2253, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10315 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10315 : lratChecker f10315 p10315 = .success := by decide +kernel
theorem unsat10315 : Unsatisfiable (PosFin 65) f10315 := by
  apply lratCheckerSound f10315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10315
  · intro a ha; simp [p10315] at ha; subst a; trivial
  · exact checked10315
theorem derived10315 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10315 := by
  apply localUnsat_implies_entails f10315 [c9748, c2253] c10315 unsat10315 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2253 := h 2252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10316 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨14, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10316 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2251, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10316 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10316 : lratChecker f10316 p10316 = .success := by decide +kernel
theorem unsat10316 : Unsatisfiable (PosFin 65) f10316 := by
  apply lratCheckerSound f10316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10316
  · intro a ha; simp [p10316] at ha; subst a; trivial
  · exact checked10316
theorem derived10316 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10316 := by
  apply localUnsat_implies_entails f10316 [c9748, c2251] c10316 unsat10316 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2251 := h 2250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10317 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10317 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2243, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10317 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10317 : lratChecker f10317 p10317 = .success := by decide +kernel
theorem unsat10317 : Unsatisfiable (PosFin 65) f10317 := by
  apply lratCheckerSound f10317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10317
  · intro a ha; simp [p10317] at ha; subst a; trivial
  · exact checked10317
theorem derived10317 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10317 := by
  apply localUnsat_implies_entails f10317 [c9748, c2243] c10317 unsat10317 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2243 := h 2242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10318 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10318 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2003, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10318 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10318 : lratChecker f10318 p10318 = .success := by decide +kernel
theorem unsat10318 : Unsatisfiable (PosFin 65) f10318 := by
  apply lratCheckerSound f10318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10318
  · intro a ha; simp [p10318] at ha; subst a; trivial
  · exact checked10318
theorem derived10318 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10318 := by
  apply localUnsat_implies_entails f10318 [c9748, c2003] c10318 unsat10318 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2003 := h 2002 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10319 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨34, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10319 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1969, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10319 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10319 : lratChecker f10319 p10319 = .success := by decide +kernel
theorem unsat10319 : Unsatisfiable (PosFin 65) f10319 := by
  apply lratCheckerSound f10319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10319
  · intro a ha; simp [p10319] at ha; subst a; trivial
  · exact checked10319
theorem derived10319 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10319 := by
  apply localUnsat_implies_entails f10319 [c9748, c1969] c10319 unsat10319 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1969 := h 1968 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10320 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨64, by decide⟩, true), (⟨14, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10320 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1795, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10320 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10320 : lratChecker f10320 p10320 = .success := by decide +kernel
theorem unsat10320 : Unsatisfiable (PosFin 65) f10320 := by
  apply lratCheckerSound f10320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10320
  · intro a ha; simp [p10320] at ha; subst a; trivial
  · exact checked10320
theorem derived10320 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10320 := by
  apply localUnsat_implies_entails f10320 [c9748, c1795] c10320 unsat10320 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1795 := h 1794 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10321 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10321 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1794, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p10321 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10321 : lratChecker f10321 p10321 = .success := by decide +kernel
theorem unsat10321 : Unsatisfiable (PosFin 65) f10321 := by
  apply lratCheckerSound f10321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10321
  · intro a ha; simp [p10321] at ha; subst a; trivial
  · exact checked10321
theorem derived10321 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10321 := by
  apply localUnsat_implies_entails f10321 [c9748, c1794] c10321 unsat10321 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1794 := h 1793 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10322 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10322 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8003, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p10322 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10322 : lratChecker f10322 p10322 = .success := by decide +kernel
theorem unsat10322 : Unsatisfiable (PosFin 65) f10322 := by
  apply lratCheckerSound f10322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10322
  · intro a ha; simp [p10322] at ha; subst a; trivial
  · exact checked10322
theorem derived10322 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10322 := by
  apply localUnsat_implies_entails f10322 [c9748, c8003] c10322 unsat10322 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8003 := derived8003 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10323 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10323 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2264, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10323 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10323 : lratChecker f10323 p10323 = .success := by decide +kernel
theorem unsat10323 : Unsatisfiable (PosFin 65) f10323 := by
  apply lratCheckerSound f10323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10323
  · intro a ha; simp [p10323] at ha; subst a; trivial
  · exact checked10323
theorem derived10323 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10323 := by
  apply localUnsat_implies_entails f10323 [c9748, c2264] c10323 unsat10323 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2264 := h 2263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10324 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨59, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10324 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2267, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p10324 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10324 : lratChecker f10324 p10324 = .success := by decide +kernel
theorem unsat10324 : Unsatisfiable (PosFin 65) f10324 := by
  apply lratCheckerSound f10324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10324
  · intro a ha; simp [p10324] at ha; subst a; trivial
  · exact checked10324
theorem derived10324 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10324 := by
  apply localUnsat_implies_entails f10324 [c9748, c2267] c10324 unsat10324 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2267 := h 2266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10325 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨36, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10325 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1718, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p10325 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10325 : lratChecker f10325 p10325 = .success := by decide +kernel
theorem unsat10325 : Unsatisfiable (PosFin 65) f10325 := by
  apply lratCheckerSound f10325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10325
  · intro a ha; simp [p10325] at ha; subst a; trivial
  · exact checked10325
theorem derived10325 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10325 := by
  apply localUnsat_implies_entails f10325 [c9748, c1718] c10325 unsat10325 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1718 := h 1717 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10326 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨56, by decide⟩, true), (⟨13, by decide⟩, true), (⟨59, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10326 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2265, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p10326 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10326 : lratChecker f10326 p10326 = .success := by decide +kernel
theorem unsat10326 : Unsatisfiable (PosFin 65) f10326 := by
  apply lratCheckerSound f10326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10326
  · intro a ha; simp [p10326] at ha; subst a; trivial
  · exact checked10326
theorem derived10326 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10326 := by
  apply localUnsat_implies_entails f10326 [c9748, c2265] c10326 unsat10326 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2265 := h 2264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10327 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨59, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10327 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2374, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10327 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10327 : lratChecker f10327 p10327 = .success := by decide +kernel
theorem unsat10327 : Unsatisfiable (PosFin 65) f10327 := by
  apply lratCheckerSound f10327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10327
  · intro a ha; simp [p10327] at ha; subst a; trivial
  · exact checked10327
theorem derived10327 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10327 := by
  apply localUnsat_implies_entails f10327 [c9748, c2374] c10327 unsat10327 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2374 := h 2373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10328 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨58, by decide⟩, true), (⟨59, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10328 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2376, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10328 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10328 : lratChecker f10328 p10328 = .success := by decide +kernel
theorem unsat10328 : Unsatisfiable (PosFin 65) f10328 := by
  apply lratCheckerSound f10328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10328
  · intro a ha; simp [p10328] at ha; subst a; trivial
  · exact checked10328
theorem derived10328 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10328 := by
  apply localUnsat_implies_entails f10328 [c9748, c2376] c10328 unsat10328 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2376 := h 2375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10329 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨57, by decide⟩, false), (⟨7, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10329 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8262, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10329 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10329 : lratChecker f10329 p10329 = .success := by decide +kernel
theorem unsat10329 : Unsatisfiable (PosFin 65) f10329 := by
  apply lratCheckerSound f10329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10329
  · intro a ha; simp [p10329] at ha; subst a; trivial
  · exact checked10329
theorem derived10329 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10329 := by
  apply localUnsat_implies_entails f10329 [c9748, c8262] c10329 unsat10329 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8262 := derived8262 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10330 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨57, by decide⟩, false), (⟨64, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10330 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1790, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10330 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10330 : lratChecker f10330 p10330 = .success := by decide +kernel
theorem unsat10330 : Unsatisfiable (PosFin 65) f10330 := by
  apply lratCheckerSound f10330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10330
  · intro a ha; simp [p10330] at ha; subst a; trivial
  · exact checked10330
theorem derived10330 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10330 := by
  apply localUnsat_implies_entails f10330 [c9748, c1790] c10330 unsat10330 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1790 := h 1789 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10331 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10331 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1788, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10331 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10331 : lratChecker f10331 p10331 = .success := by decide +kernel
theorem unsat10331 : Unsatisfiable (PosFin 65) f10331 := by
  apply lratCheckerSound f10331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10331
  · intro a ha; simp [p10331] at ha; subst a; trivial
  · exact checked10331
theorem derived10331 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10331 := by
  apply localUnsat_implies_entails f10331 [c9748, c1788] c10331 unsat10331 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1788 := h 1787 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10332 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10332 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1789, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10332 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10332 : lratChecker f10332 p10332 = .success := by decide +kernel
theorem unsat10332 : Unsatisfiable (PosFin 65) f10332 := by
  apply lratCheckerSound f10332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10332
  · intro a ha; simp [p10332] at ha; subst a; trivial
  · exact checked10332
theorem derived10332 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10332 := by
  apply localUnsat_implies_entails f10332 [c9748, c1789] c10332 unsat10332 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1789 := h 1788 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10333 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨61, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10333 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1738, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10333 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10333 : lratChecker f10333 p10333 = .success := by decide +kernel
theorem unsat10333 : Unsatisfiable (PosFin 65) f10333 := by
  apply lratCheckerSound f10333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10333
  · intro a ha; simp [p10333] at ha; subst a; trivial
  · exact checked10333
theorem derived10333 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10333 := by
  apply localUnsat_implies_entails f10333 [c9748, c1738] c10333 unsat10333 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1738 := h 1737 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10334 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨14, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10334 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1810, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10334 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10334 : lratChecker f10334 p10334 = .success := by decide +kernel
theorem unsat10334 : Unsatisfiable (PosFin 65) f10334 := by
  apply lratCheckerSound f10334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10334
  · intro a ha; simp [p10334] at ha; subst a; trivial
  · exact checked10334
theorem derived10334 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10334 := by
  apply localUnsat_implies_entails f10334 [c9748, c1810] c10334 unsat10334 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1810 := h 1809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10335 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨59, by decide⟩, false), (⟨51, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10335 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1894, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p10335 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10335 : lratChecker f10335 p10335 = .success := by decide +kernel
theorem unsat10335 : Unsatisfiable (PosFin 65) f10335 := by
  apply lratCheckerSound f10335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10335
  · intro a ha; simp [p10335] at ha; subst a; trivial
  · exact checked10335
theorem derived10335 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10335 := by
  apply localUnsat_implies_entails f10335 [c9748, c1894] c10335 unsat10335 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1894 := h 1893 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10336 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨59, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10336 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1813, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10336 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10336 : lratChecker f10336 p10336 = .success := by decide +kernel
theorem unsat10336 : Unsatisfiable (PosFin 65) f10336 := by
  apply lratCheckerSound f10336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10336
  · intro a ha; simp [p10336] at ha; subst a; trivial
  · exact checked10336
theorem derived10336 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10336 := by
  apply localUnsat_implies_entails f10336 [c9748, c1813] c10336 unsat10336 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1813 := h 1812 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10337 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10337 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1815, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10337 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10337 : lratChecker f10337 p10337 = .success := by decide +kernel
theorem unsat10337 : Unsatisfiable (PosFin 65) f10337 := by
  apply lratCheckerSound f10337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10337
  · intro a ha; simp [p10337] at ha; subst a; trivial
  · exact checked10337
theorem derived10337 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10337 := by
  apply localUnsat_implies_entails f10337 [c9748, c1815] c10337 unsat10337 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1815 := h 1814 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10338 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨6, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10338 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1746, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10338 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10338 : lratChecker f10338 p10338 = .success := by decide +kernel
theorem unsat10338 : Unsatisfiable (PosFin 65) f10338 := by
  apply lratCheckerSound f10338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10338
  · intro a ha; simp [p10338] at ha; subst a; trivial
  · exact checked10338
theorem derived10338 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10338 := by
  apply localUnsat_implies_entails f10338 [c9748, c1746] c10338 unsat10338 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1746 := h 1745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10339 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, true), (⟨14, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10339 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1786, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p10339 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10339 : lratChecker f10339 p10339 = .success := by decide +kernel
theorem unsat10339 : Unsatisfiable (PosFin 65) f10339 := by
  apply lratCheckerSound f10339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10339
  · intro a ha; simp [p10339] at ha; subst a; trivial
  · exact checked10339
theorem derived10339 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10339 := by
  apply localUnsat_implies_entails f10339 [c9748, c1786] c10339 unsat10339 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1786 := h 1785 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10340 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10340 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1814, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p10340 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10340 : lratChecker f10340 p10340 = .success := by decide +kernel
theorem unsat10340 : Unsatisfiable (PosFin 65) f10340 := by
  apply lratCheckerSound f10340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10340
  · intro a ha; simp [p10340] at ha; subst a; trivial
  · exact checked10340
theorem derived10340 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10340 := by
  apply localUnsat_implies_entails f10340 [c9748, c1814] c10340 unsat10340 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1814 := h 1813 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10341 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨14, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10341 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1809, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10341 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10341 : lratChecker f10341 p10341 = .success := by decide +kernel
theorem unsat10341 : Unsatisfiable (PosFin 65) f10341 := by
  apply lratCheckerSound f10341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10341
  · intro a ha; simp [p10341] at ha; subst a; trivial
  · exact checked10341
theorem derived10341 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10341 := by
  apply localUnsat_implies_entails f10341 [c9748, c1809] c10341 unsat10341 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1809 := h 1808 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10342 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨14, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10342 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1793, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10342 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10342 : lratChecker f10342 p10342 = .success := by decide +kernel
theorem unsat10342 : Unsatisfiable (PosFin 65) f10342 := by
  apply lratCheckerSound f10342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10342
  · intro a ha; simp [p10342] at ha; subst a; trivial
  · exact checked10342
theorem derived10342 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10342 := by
  apply localUnsat_implies_entails f10342 [c9748, c1793] c10342 unsat10342 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1793 := h 1792 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10343 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨14, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10343 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1785, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10343 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10343 : lratChecker f10343 p10343 = .success := by decide +kernel
theorem unsat10343 : Unsatisfiable (PosFin 65) f10343 := by
  apply lratCheckerSound f10343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10343
  · intro a ha; simp [p10343] at ha; subst a; trivial
  · exact checked10343
theorem derived10343 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10343 := by
  apply localUnsat_implies_entails f10343 [c9748, c1785] c10343 unsat10343 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1785 := h 1784 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10344 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10344 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1817, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10344 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10344 : lratChecker f10344 p10344 = .success := by decide +kernel
theorem unsat10344 : Unsatisfiable (PosFin 65) f10344 := by
  apply lratCheckerSound f10344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10344
  · intro a ha; simp [p10344] at ha; subst a; trivial
  · exact checked10344
theorem derived10344 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10344 := by
  apply localUnsat_implies_entails f10344 [c9748, c1817] c10344 unsat10344 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1817 := h 1816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10345 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10345 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1811, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10345 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10345 : lratChecker f10345 p10345 = .success := by decide +kernel
theorem unsat10345 : Unsatisfiable (PosFin 65) f10345 := by
  apply lratCheckerSound f10345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10345
  · intro a ha; simp [p10345] at ha; subst a; trivial
  · exact checked10345
theorem derived10345 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10345 := by
  apply localUnsat_implies_entails f10345 [c9748, c1811] c10345 unsat10345 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1811 := h 1810 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10346 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10346 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1800, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10346 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10346 : lratChecker f10346 p10346 = .success := by decide +kernel
theorem unsat10346 : Unsatisfiable (PosFin 65) f10346 := by
  apply lratCheckerSound f10346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10346
  · intro a ha; simp [p10346] at ha; subst a; trivial
  · exact checked10346
theorem derived10346 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10346 := by
  apply localUnsat_implies_entails f10346 [c9748, c1800] c10346 unsat10346 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1800 := h 1799 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10347 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10347 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1807, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10347 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10347 : lratChecker f10347 p10347 = .success := by decide +kernel
theorem unsat10347 : Unsatisfiable (PosFin 65) f10347 := by
  apply lratCheckerSound f10347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10347
  · intro a ha; simp [p10347] at ha; subst a; trivial
  · exact checked10347
theorem derived10347 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10347 := by
  apply localUnsat_implies_entails f10347 [c9748, c1807] c10347 unsat10347 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1807 := h 1806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10348 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10348 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1897, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10348 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10348 : lratChecker f10348 p10348 = .success := by decide +kernel
theorem unsat10348 : Unsatisfiable (PosFin 65) f10348 := by
  apply lratCheckerSound f10348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10348
  · intro a ha; simp [p10348] at ha; subst a; trivial
  · exact checked10348
theorem derived10348 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10348 := by
  apply localUnsat_implies_entails f10348 [c9748, c1897] c10348 unsat10348 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1897 := h 1896 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10349 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10349 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1899, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10349 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10349 : lratChecker f10349 p10349 = .success := by decide +kernel
theorem unsat10349 : Unsatisfiable (PosFin 65) f10349 := by
  apply lratCheckerSound f10349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10349
  · intro a ha; simp [p10349] at ha; subst a; trivial
  · exact checked10349
theorem derived10349 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10349 := by
  apply localUnsat_implies_entails f10349 [c9748, c1899] c10349 unsat10349 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1899 := h 1898 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10350 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10350 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1727, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10350 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10350 : lratChecker f10350 p10350 = .success := by decide +kernel
theorem unsat10350 : Unsatisfiable (PosFin 65) f10350 := by
  apply lratCheckerSound f10350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10350
  · intro a ha; simp [p10350] at ha; subst a; trivial
  · exact checked10350
theorem derived10350 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10350 := by
  apply localUnsat_implies_entails f10350 [c9748, c1727] c10350 unsat10350 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1727 := h 1726 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived10350

end CochromaticTwenty.Certificates.FixedCore0
