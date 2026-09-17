import MerLeanExperiment.Certificates.Z12Direct_5_8_6.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_8_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c426 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f426 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c266, some c56, some c103, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p426 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked426 : lratChecker f426 p426 = .success := by decide +kernel
theorem unsat426 : Unsatisfiable (PosFin 31) f426 := by
  apply lratCheckerSound f426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p426
  · intro a ha; simp [p426] at ha; subst a; trivial
  · exact checked426
theorem derived426 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c426 := by
  apply localUnsat_implies_entails f426 [c382, c266, c56, c103] c426 unsat426 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c427 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f427 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c424, some c4, some c425, some c182, some c2, some c185, some c157, some c53, some c93, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p427 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked427 : lratChecker f427 p427 = .success := by decide +kernel
theorem unsat427 : Unsatisfiable (PosFin 31) f427 := by
  apply lratCheckerSound f427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p427
  · intro a ha; simp [p427] at ha; subst a; trivial
  · exact checked427
theorem derived427 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c427 := by
  apply localUnsat_implies_entails f427 [c382, c424, c4, c425, c182, c2, c185, c157, c53, c93] c427 unsat427 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c424 := derived424 a h
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c425 := derived425 a h
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c428 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f428 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c427, some c182, some c267, some c169, some c245, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p428 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked428 : lratChecker f428 p428 = .success := by decide +kernel
theorem unsat428 : Unsatisfiable (PosFin 31) f428 := by
  apply lratCheckerSound f428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p428
  · intro a ha; simp [p428] at ha; subst a; trivial
  · exact checked428
theorem derived428 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c428 := by
  apply localUnsat_implies_entails f428 [c424, c427, c182, c267, c169, c245] c428 unsat428 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c427 := derived427 a h
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c429 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c427, some c428, some c264, some c225, some c245, some c32, some c169, some c73, some c206, some c62, some c192, some c390, some c67, some c82, some c224, some c321, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p429 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 31) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c424, c427, c428, c264, c225, c245, c32, c169, c73, c206, c62, c192, c390, c67, c82, c224, c321] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c427 := derived427 a h
  have h2 : Entails.eval a c428 := derived428 a h
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c225 := h 224 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c390 := derived390 a h
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c224 := h 223 (by decide)
  have h16 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c430 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c241, some c271, some c252, some c232, some c215, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p430 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 31) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c424, c241, c271, c252, c232, c215] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c232 := h 231 (by decide)
  have h5 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c431 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c429, some c427, some c192, some c430, some c34, some c364, some c10, some c154, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p431 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 31) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c424, c429, c427, c192, c430, c34, c364, c10, c154] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c427 := derived427 a h
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c430 := derived430 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c364 := derived364 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c432 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c429, some c245, some c247, some c194, some c3, some c212, some c147, some c10, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p432 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 31) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c424, c429, c245, c247, c194, c3, c212, c147, c10] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c245 := h 244 (by decide)
  have h3 : Entails.eval a c247 := h 246 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c429, some c431, some c432, some c56, some c271, some c232, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p433 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 31) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c382, c429, c431, c432, c56, c271, c232] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c431 := derived431 a h
  have h3 : Entails.eval a c432 := derived432 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c427, some c433, some c182, some c267, some c426, some c245, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p434 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 31) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c424, c427, c433, c182, c267, c426, c245] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c427 := derived427 a h
  have h2 : Entails.eval a c433 := derived433 a h
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c426 := derived426 a h
  have h6 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c435 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c424, some c434, some c172, some c88, some c37, some c185, some c267, some c186, some c268, some c298, some c281, some c189, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p435 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 31) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c382, c424, c434, c172, c88, c37, c185, c267, c186, c268, c298, c281, c189] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c424 := derived424 a h
  have h2 : Entails.eval a c434 := derived434 a h
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c298 := h 297 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c434, some c192, some c189, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p436 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 31) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c424, c434, c192, c189] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c434 := derived434 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c382, some c436, some c434, some c172, some c37, some c247, some c88, some c435, some c281, some c153, some c26, some c7, some c297, some c223, some c47, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p437 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 31) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c424, c382, c436, c434, c172, c37, c247, c88, c435, c281, c153, c26, c7, c297, c223, c47] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c434 := derived434 a h
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c247 := h 246 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c435 := derived435 a h
  have h9 : Entails.eval a c281 := h 280 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c7 := h 6 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c223 := h 222 (by decide)
  have h15 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c438 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c436, some c437, some c56, some c426, some c434, some c26, some c297, some c223, some c47, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p438 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 31) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c382, c436, c437, c56, c426, c434, c26, c297, c223, c47] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c436 := derived436 a h
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c426 := derived426 a h
  have h5 : Entails.eval a c434 := derived434 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c424, some c436, some c437, some c56, some c103, some c426, some c434, some c28, some c209, some c230, some c222, some c263, some c256, some c97, some c114, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p439 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 31) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c382, c424, c436, c437, c56, c103, c426, c434, c28, c209, c230, c222, c263, c256, c97, c114] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c424 := derived424 a h
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c426 := derived426 a h
  have h7 : Entails.eval a c434 := derived434 a h
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c256 := h 255 (by decide)
  have h14 : Entails.eval a c97 := h 96 (by decide)
  have h15 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c440 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c382, some c434, some c439, some c283, some c438, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p440 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 31) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c424, c382, c434, c439, c283, c438] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c434 := derived434 a h
  have h3 : Entails.eval a c439 := derived439 a h
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c438 := derived438 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c441 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c382, some c437, some c436, some c434, some c440, some c281, some c190, some c283, some c246, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p441 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 31) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c424, c382, c437, c436, c434, c440, c281, c190, c283, c246] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c436 := derived436 a h
  have h4 : Entails.eval a c434 := derived434 a h
  have h5 : Entails.eval a c440 := derived440 a h
  have h6 : Entails.eval a c281 := h 280 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c382, some c437, some c436, some c56, some c103, some c441, some c296, some c434, some c39, some c190, some c275, some c295, some c81, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p442 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 31) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c424, c382, c437, c436, c56, c103, c441, c296, c434, c39, c190, c275, c295, c81] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c436 := derived436 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c441 := derived441 a h
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c434 := derived434 a h
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c190 := h 189 (by decide)
  have h11 : Entails.eval a c275 := h 274 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c443 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c441, some c436, some c437, some c426, some c442, some c315, some c26, some c262, some c276, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p443 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 31) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c382, c441, c436, c437, c426, c442, c315, c26, c262, c276] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c441 := derived441 a h
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c426 := derived426 a h
  have h5 : Entails.eval a c442 := derived442 a h
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c262 := h 261 (by decide)
  have h9 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c444 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f444 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c441, some c436, some c437, some c56, some c426, some c434, some c442, some c315, some c443, some c209, some c208, some c230, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p444 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked444 : lratChecker f444 p444 = .success := by decide +kernel
theorem unsat444 : Unsatisfiable (PosFin 31) f444 := by
  apply lratCheckerSound f444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p444
  · intro a ha; simp [p444] at ha; subst a; trivial
  · exact checked444
theorem derived444 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c444 := by
  apply localUnsat_implies_entails f444 [c382, c441, c436, c437, c56, c426, c434, c442, c315, c443, c209, c208, c230] c444 unsat444 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c441 := derived441 a h
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c426 := derived426 a h
  have h6 : Entails.eval a c434 := derived434 a h
  have h7 : Entails.eval a c442 := derived442 a h
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c443 := derived443 a h
  have h10 : Entails.eval a c209 := h 208 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c445 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f445 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c382, some c436, some c437, some c56, some c103, some c426, some c434, some c444, some c12, some c179, some c94, some c169, some c18, some c251, some c241, some c314, some c131, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p445 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked445 : lratChecker f445 p445 = .success := by decide +kernel
theorem unsat445 : Unsatisfiable (PosFin 31) f445 := by
  apply lratCheckerSound f445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p445
  · intro a ha; simp [p445] at ha; subst a; trivial
  · exact checked445
theorem derived445 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c445 := by
  apply localUnsat_implies_entails f445 [c424, c382, c436, c437, c56, c103, c426, c434, c444, c12, c179, c94, c169, c18, c251, c241, c314, c131] c445 unsat445 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c426 := derived426 a h
  have h7 : Entails.eval a c434 := derived434 a h
  have h8 : Entails.eval a c444 := derived444 a h
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c18 := h 17 (by decide)
  have h14 : Entails.eval a c251 := h 250 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  have h16 : Entails.eval a c314 := h 313 (by decide)
  have h17 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c446 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f446 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c445, some c15, some c436, some c437, some c56, some c103, some c434, some c293, some c47, some c46, some c313, some c117, some c323, some c40, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p446 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked446 : lratChecker f446 p446 = .success := by decide +kernel
theorem unsat446 : Unsatisfiable (PosFin 31) f446 := by
  apply lratCheckerSound f446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p446
  · intro a ha; simp [p446] at ha; subst a; trivial
  · exact checked446
theorem derived446 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c446 := by
  apply localUnsat_implies_entails f446 [c382, c445, c15, c436, c437, c56, c103, c434, c293, c47, c46, c313, c117, c323, c40] c446 unsat446 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c445 := derived445 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c436 := derived436 a h
  have h4 : Entails.eval a c437 := derived437 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c434 := derived434 a h
  have h8 : Entails.eval a c293 := h 292 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c46 := h 45 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c447 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f447 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c382, some c445, some c15, some c436, some c437, some c56, some c103, some c47, some c46, some c117, some c94, some c40, some c91, some c323, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p447 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked447 : lratChecker f447 p447 = .success := by decide +kernel
theorem unsat447 : Unsatisfiable (PosFin 31) f447 := by
  apply lratCheckerSound f447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p447
  · intro a ha; simp [p447] at ha; subst a; trivial
  · exact checked447
theorem derived447 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c447 := by
  apply localUnsat_implies_entails f447 [c424, c382, c445, c15, c436, c437, c56, c103, c47, c46, c117, c94, c40, c91, c323] c447 unsat447 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c445 := derived445 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c436 := derived436 a h
  have h5 : Entails.eval a c437 := derived437 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c91 := h 90 (by decide)
  have h14 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c448 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f448 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c436, some c437, some c56, some c103, some c445, some c15, some c446, some c447, some c318, some c309, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p448 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked448 : lratChecker f448 p448 = .success := by decide +kernel
theorem unsat448 : Unsatisfiable (PosFin 31) f448 := by
  apply lratCheckerSound f448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p448
  · intro a ha; simp [p448] at ha; subst a; trivial
  · exact checked448
theorem derived448 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c448 := by
  apply localUnsat_implies_entails f448 [c382, c436, c437, c56, c103, c445, c15, c446, c447, c318, c309] c448 unsat448 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c436 := derived436 a h
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c445 := derived445 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c446 := derived446 a h
  have h8 : Entails.eval a c447 := derived447 a h
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c449 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f449 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c448, some c424, some c382, some c175, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p449 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked449 : lratChecker f449 p449 = .success := by decide +kernel
theorem unsat449 : Unsatisfiable (PosFin 31) f449 := by
  apply lratCheckerSound f449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p449
  · intro a ha; simp [p449] at ha; subst a; trivial
  · exact checked449
theorem derived449 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c449 := by
  apply localUnsat_implies_entails f449 [c448, c424, c382, c175] c449 unsat449 (by rfl) a
  have h0 : Entails.eval a c448 := derived448 a h
  have h1 : Entails.eval a c424 := derived424 a h
  have h2 : Entails.eval a c382 := derived382 a h
  have h3 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c450 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f450 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c382, some c448, some c173, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p450 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked450 : lratChecker f450 p450 = .success := by decide +kernel
theorem unsat450 : Unsatisfiable (PosFin 31) f450 := by
  apply lratCheckerSound f450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p450
  · intro a ha; simp [p450] at ha; subst a; trivial
  · exact checked450
theorem derived450 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c450 := by
  apply localUnsat_implies_entails f450 [c449, c382, c448, c173] c450 unsat450 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c448 := derived448 a h
  have h3 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c451 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f451 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c450, some c448, some c382, some c174, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p451 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked451 : lratChecker f451 p451 = .success := by decide +kernel
theorem unsat451 : Unsatisfiable (PosFin 31) f451 := by
  apply lratCheckerSound f451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p451
  · intro a ha; simp [p451] at ha; subst a; trivial
  · exact checked451
theorem derived451 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c451 := by
  apply localUnsat_implies_entails f451 [c450, c448, c382, c174] c451 unsat451 (by rfl) a
  have h0 : Entails.eval a c450 := derived450 a h
  have h1 : Entails.eval a c448 := derived448 a h
  have h2 : Entails.eval a c382 := derived382 a h
  have h3 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c452 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f452 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c451, some c449, some c424, some c382, some c448, some c272, some c18, some c251, some c241, some c271, some c274, some c306, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p452 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked452 : lratChecker f452 p452 = .success := by decide +kernel
theorem unsat452 : Unsatisfiable (PosFin 31) f452 := by
  apply lratCheckerSound f452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p452
  · intro a ha; simp [p452] at ha; subst a; trivial
  · exact checked452
theorem derived452 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c452 := by
  apply localUnsat_implies_entails f452 [c451, c449, c424, c382, c448, c272, c18, c251, c241, c271, c274, c306] c452 unsat452 (by rfl) a
  have h0 : Entails.eval a c451 := derived451 a h
  have h1 : Entails.eval a c449 := derived449 a h
  have h2 : Entails.eval a c424 := derived424 a h
  have h3 : Entails.eval a c382 := derived382 a h
  have h4 : Entails.eval a c448 := derived448 a h
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c453 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f453 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c448, some c382, some c103, some c233, some c102, some c232, some c14, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p453 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked453 : lratChecker f453 p453 = .success := by decide +kernel
theorem unsat453 : Unsatisfiable (PosFin 31) f453 := by
  apply lratCheckerSound f453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p453
  · intro a ha; simp [p453] at ha; subst a; trivial
  · exact checked453
theorem derived453 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c453 := by
  apply localUnsat_implies_entails f453 [c448, c382, c103, c233, c102, c232, c14] c453 unsat453 (by rfl) a
  have h0 : Entails.eval a c448 := derived448 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c454 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f454 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c451, some c449, some c424, some c448, some c453, some c272, some c18, some c452, some c241, some c271, some c251, some c235, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p454 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked454 : lratChecker f454 p454 = .success := by decide +kernel
theorem unsat454 : Unsatisfiable (PosFin 31) f454 := by
  apply lratCheckerSound f454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p454
  · intro a ha; simp [p454] at ha; subst a; trivial
  · exact checked454
theorem derived454 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c454 := by
  apply localUnsat_implies_entails f454 [c451, c449, c424, c448, c453, c272, c18, c452, c241, c271, c251, c235] c454 unsat454 (by rfl) a
  have h0 : Entails.eval a c451 := derived451 a h
  have h1 : Entails.eval a c449 := derived449 a h
  have h2 : Entails.eval a c424 := derived424 a h
  have h3 : Entails.eval a c448 := derived448 a h
  have h4 : Entails.eval a c453 := derived453 a h
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c452 := derived452 a h
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c455 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f455 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c454, some c449, some c382, some c56, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p455 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked455 : lratChecker f455 p455 = .success := by decide +kernel
theorem unsat455 : Unsatisfiable (PosFin 31) f455 := by
  apply lratCheckerSound f455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p455
  · intro a ha; simp [p455] at ha; subst a; trivial
  · exact checked455
theorem derived455 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c455 := by
  apply localUnsat_implies_entails f455 [c454, c449, c382, c56] c455 unsat455 (by rfl) a
  have h0 : Entails.eval a c454 := derived454 a h
  have h1 : Entails.eval a c449 := derived449 a h
  have h2 : Entails.eval a c382 := derived382 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c456 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f456 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c454, some c451, some c449, some c32, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p456 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked456 : lratChecker f456 p456 = .success := by decide +kernel
theorem unsat456 : Unsatisfiable (PosFin 31) f456 := by
  apply lratCheckerSound f456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p456
  · intro a ha; simp [p456] at ha; subst a; trivial
  · exact checked456
theorem derived456 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c456 := by
  apply localUnsat_implies_entails f456 [c454, c451, c449, c32] c456 unsat456 (by rfl) a
  have h0 : Entails.eval a c454 := derived454 a h
  have h1 : Entails.eval a c451 := derived451 a h
  have h2 : Entails.eval a c449 := derived449 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c457 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f457 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c454, some c455, some c449, some c55, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p457 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked457 : lratChecker f457 p457 = .success := by decide +kernel
theorem unsat457 : Unsatisfiable (PosFin 31) f457 := by
  apply lratCheckerSound f457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p457
  · intro a ha; simp [p457] at ha; subst a; trivial
  · exact checked457
theorem derived457 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c457 := by
  apply localUnsat_implies_entails f457 [c454, c455, c449, c55] c457 unsat457 (by rfl) a
  have h0 : Entails.eval a c454 := derived454 a h
  have h1 : Entails.eval a c455 := derived455 a h
  have h2 : Entails.eval a c449 := derived449 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c458 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f458 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c455, some c451, some c449, some c90, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p458 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked458 : lratChecker f458 p458 = .success := by decide +kernel
theorem unsat458 : Unsatisfiable (PosFin 31) f458 := by
  apply lratCheckerSound f458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p458
  · intro a ha; simp [p458] at ha; subst a; trivial
  · exact checked458
theorem derived458 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c458 := by
  apply localUnsat_implies_entails f458 [c455, c451, c449, c90] c458 unsat458 (by rfl) a
  have h0 : Entails.eval a c455 := derived455 a h
  have h1 : Entails.eval a c451 := derived451 a h
  have h2 : Entails.eval a c449 := derived449 a h
  have h3 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c459 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f459 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c456, some c455, some c424, some c71, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p459 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked459 : lratChecker f459 p459 = .success := by decide +kernel
theorem unsat459 : Unsatisfiable (PosFin 31) f459 := by
  apply lratCheckerSound f459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p459
  · intro a ha; simp [p459] at ha; subst a; trivial
  · exact checked459
theorem derived459 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c459 := by
  apply localUnsat_implies_entails f459 [c456, c455, c424, c71] c459 unsat459 (by rfl) a
  have h0 : Entails.eval a c456 := derived456 a h
  have h1 : Entails.eval a c455 := derived455 a h
  have h2 : Entails.eval a c424 := derived424 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c460 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f460 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c457, some c448, some c382, some c14, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p460 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked460 : lratChecker f460 p460 = .success := by decide +kernel
theorem unsat460 : Unsatisfiable (PosFin 31) f460 := by
  apply lratCheckerSound f460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p460
  · intro a ha; simp [p460] at ha; subst a; trivial
  · exact checked460
theorem derived460 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c460 := by
  apply localUnsat_implies_entails f460 [c457, c448, c382, c14] c460 unsat460 (by rfl) a
  have h0 : Entails.eval a c457 := derived457 a h
  have h1 : Entails.eval a c448 := derived448 a h
  have h2 : Entails.eval a c382 := derived382 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c461 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f461 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c459, some c460, some c458, some c205, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p461 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked461 : lratChecker f461 p461 = .success := by decide +kernel
theorem unsat461 : Unsatisfiable (PosFin 31) f461 := by
  apply lratCheckerSound f461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p461
  · intro a ha; simp [p461] at ha; subst a; trivial
  · exact checked461
theorem derived461 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c461 := by
  apply localUnsat_implies_entails f461 [c459, c460, c458, c205] c461 unsat461 (by rfl) a
  have h0 : Entails.eval a c459 := derived459 a h
  have h1 : Entails.eval a c460 := derived460 a h
  have h2 : Entails.eval a c458 := derived458 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c462 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f462 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c459, some c461, some c458, some c457, some c121]
def p462 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked462 : lratChecker f462 p462 = .success := by decide +kernel
theorem unsat462 : Unsatisfiable (PosFin 31) f462 := by
  apply lratCheckerSound f462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p462
  · intro a ha; simp [p462] at ha; subst a; trivial
  · exact checked462
theorem derived462 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c462 := by
  apply localUnsat_implies_entails f462 [c459, c461, c458, c457, c121] c462 unsat462 (by rfl) a
  have h0 : Entails.eval a c459 := derived459 a h
  have h1 : Entails.eval a c461 := derived461 a h
  have h2 : Entails.eval a c458 := derived458 a h
  have h3 : Entails.eval a c457 := derived457 a h
  have h4 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived462

end CochromaticTwenty.Certificates.Z12Direct_5_8_6
