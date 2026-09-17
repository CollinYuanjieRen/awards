import MerLeanExperiment.Certificates.Z12Direct_5_4_11.Inputs

/-! Generated from the actual pinned z12direct_5_4_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c274 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f274 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c227, some c57, some c59, some c51, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p274 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked274 : lratChecker f274 p274 = .success := by decide +kernel
theorem unsat274 : Unsatisfiable (PosFin 31) f274 := by
  apply lratCheckerSound f274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p274
  · intro a ha; simp [p274] at ha; subst a; trivial
  · exact checked274
theorem derived274 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c274 := by
  apply localUnsat_implies_entails f274 [c209, c227, c57, c59, c51] c274 unsat274 (by rfl) a
  have h0 : Entails.eval a c209 := h 208 (by decide)
  have h1 : Entails.eval a c227 := h 226 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c275 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f275 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c245, some c261, some c57, some c59, some c51, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p275 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked275 : lratChecker f275 p275 = .success := by decide +kernel
theorem unsat275 : Unsatisfiable (PosFin 31) f275 := by
  apply lratCheckerSound f275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p275
  · intro a ha; simp [p275] at ha; subst a; trivial
  · exact checked275
theorem derived275 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c275 := by
  apply localUnsat_implies_entails f275 [c245, c261, c57, c59, c51] c275 unsat275 (by rfl) a
  have h0 : Entails.eval a c245 := h 244 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c276 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f276 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c61, some c63, some c274, some c174, some c275, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p276 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked276 : lratChecker f276 p276 = .success := by decide +kernel
theorem unsat276 : Unsatisfiable (PosFin 31) f276 := by
  apply lratCheckerSound f276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p276
  · intro a ha; simp [p276] at ha; subst a; trivial
  · exact checked276
theorem derived276 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c276 := by
  apply localUnsat_implies_entails f276 [c61, c63, c274, c174, c275] c276 unsat276 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c274 := derived274 a h
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c275 := derived275 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c277 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f277 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c274, some c275, some c56, some c58, some c51, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p277 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked277 : lratChecker f277 p277 = .success := by decide +kernel
theorem unsat277 : Unsatisfiable (PosFin 31) f277 := by
  apply lratCheckerSound f277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p277
  · intro a ha; simp [p277] at ha; subst a; trivial
  · exact checked277
theorem derived277 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c277 := by
  apply localUnsat_implies_entails f277 [c274, c275, c56, c58, c51] c277 unsat277 (by rfl) a
  have h0 : Entails.eval a c274 := derived274 a h
  have h1 : Entails.eval a c275 := derived275 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c278 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨13, by decide⟩, true), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f278 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c90, some c69, some c1, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p278 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked278 : lratChecker f278 p278 = .success := by decide +kernel
theorem unsat278 : Unsatisfiable (PosFin 31) f278 := by
  apply lratCheckerSound f278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p278
  · intro a ha; simp [p278] at ha; subst a; trivial
  · exact checked278
theorem derived278 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c278 := by
  apply localUnsat_implies_entails f278 [c90, c69, c1] c278 unsat278 (by rfl) a
  have h0 : Entails.eval a c90 := h 89 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c279 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨13, by decide⟩, true), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f279 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c278, some c66, some c85, some c74, some c99, some c1, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p279 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked279 : lratChecker f279 p279 = .success := by decide +kernel
theorem unsat279 : Unsatisfiable (PosFin 31) f279 := by
  apply lratCheckerSound f279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p279
  · intro a ha; simp [p279] at ha; subst a; trivial
  · exact checked279
theorem derived279 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c279 := by
  apply localUnsat_implies_entails f279 [c278, c66, c85, c74, c99, c1] c279 unsat279 (by rfl) a
  have h0 : Entails.eval a c278 := derived278 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c280 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f280 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c47, some c60, some c276, some c265, some c1, some c77, some c68, some c32, some c24, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p280 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked280 : lratChecker f280 p280 = .success := by decide +kernel
theorem unsat280 : Unsatisfiable (PosFin 31) f280 := by
  apply lratCheckerSound f280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p280
  · intro a ha; simp [p280] at ha; subst a; trivial
  · exact checked280
theorem derived280 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c280 := by
  apply localUnsat_implies_entails f280 [c47, c60, c276, c265, c1, c77, c68, c32, c24] c280 unsat280 (by rfl) a
  have h0 : Entails.eval a c47 := h 46 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c281 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨21, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f281 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c60, some c244, some c259, some c56, some c176, some c47, some c279, some c280, some c11, some c89, some c10, some c9, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p281 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked281 : lratChecker f281 p281 = .success := by decide +kernel
theorem unsat281 : Unsatisfiable (PosFin 31) f281 := by
  apply lratCheckerSound f281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p281
  · intro a ha; simp [p281] at ha; subst a; trivial
  · exact checked281
theorem derived281 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c281 := by
  apply localUnsat_implies_entails f281 [c276, c60, c244, c259, c56, c176, c47, c279, c280, c11, c89, c10, c9] c281 unsat281 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c279 := derived279 a h
  have h8 : Entails.eval a c280 := derived280 a h
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c282 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f282 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c11, some c10, some c102, some c9, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p282 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked282 : lratChecker f282 p282 = .success := by decide +kernel
theorem unsat282 : Unsatisfiable (PosFin 31) f282 := by
  apply lratCheckerSound f282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p282
  · intro a ha; simp [p282] at ha; subst a; trivial
  · exact checked282
theorem derived282 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c282 := by
  apply localUnsat_implies_entails f282 [c11, c10, c102, c9] c282 unsat282 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c283 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨18, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f283 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c244, some c259, some c87, some c56, some c176, some c57, some c279, some c282, some c265, some c230, some c183, some c189, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p283 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked283 : lratChecker f283 p283 = .success := by decide +kernel
theorem unsat283 : Unsatisfiable (PosFin 31) f283 := by
  apply lratCheckerSound f283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p283
  · intro a ha; simp [p283] at ha; subst a; trivial
  · exact checked283
theorem derived283 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c283 := by
  apply localUnsat_implies_entails f283 [c276, c244, c259, c87, c56, c176, c57, c279, c282, c265, c230, c183, c189] c283 unsat283 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c244 := h 243 (by decide)
  have h2 : Entails.eval a c259 := h 258 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c279 := derived279 a h
  have h8 : Entails.eval a c282 := derived282 a h
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c284 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f284 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c60, some c276, some c244, some c259, some c56, some c176, some c57, some c281, some c87, some c283, some c41, some c39, some c108, some c177, some c194, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p284 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked284 : lratChecker f284 p284 = .success := by decide +kernel
theorem unsat284 : Unsatisfiable (PosFin 31) f284 := by
  apply lratCheckerSound f284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p284
  · intro a ha; simp [p284] at ha; subst a; trivial
  · exact checked284
theorem derived284 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c284 := by
  apply localUnsat_implies_entails f284 [c60, c276, c244, c259, c56, c176, c57, c281, c87, c283, c41, c39, c108, c177, c194] c284 unsat284 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c281 := derived281 a h
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c283 := derived283 a h
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c177 := h 176 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c285 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f285 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c60, some c284, some c52, some c226, some c259, some c57, some c46, some c40, some c86, some c109, some c196, some c180, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p285 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked285 : lratChecker f285 p285 = .success := by decide +kernel
theorem unsat285 : Unsatisfiable (PosFin 31) f285 := by
  apply lratCheckerSound f285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p285
  · intro a ha; simp [p285] at ha; subst a; trivial
  · exact checked285
theorem derived285 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c285 := by
  apply localUnsat_implies_entails f285 [c276, c60, c284, c52, c226, c259, c57, c46, c40, c86, c109, c196, c180] c285 unsat285 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c284 := derived284 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c226 := h 225 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c286 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f286 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c256, some c258, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p286 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked286 : lratChecker f286 p286 = .success := by decide +kernel
theorem unsat286 : Unsatisfiable (PosFin 31) f286 := by
  apply lratCheckerSound f286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p286
  · intro a ha; simp [p286] at ha; subst a; trivial
  · exact checked286
theorem derived286 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c286 := by
  apply localUnsat_implies_entails f286 [c256, c258] c286 unsat286 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c287 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f287 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c52, some c57, some c176, some c277, some c86, some c286, some c32, some c137, some c191, some c204, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p287 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked287 : lratChecker f287 p287 = .success := by decide +kernel
theorem unsat287 : Unsatisfiable (PosFin 31) f287 := by
  apply lratCheckerSound f287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p287
  · intro a ha; simp [p287] at ha; subst a; trivial
  · exact checked287
theorem derived287 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c287 := by
  apply localUnsat_implies_entails f287 [c276, c52, c57, c176, c277, c86, c286, c32, c137, c191, c204] c287 unsat287 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c277 := derived277 a h
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c286 := derived286 a h
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c191 := h 190 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c288 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f288 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c277, some c60, some c284, some c52, some c226, some c259, some c57, some c176, some c285, some c287, some c278, some c66, some c74, some c78, some c216, some c217, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p288 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked288 : lratChecker f288 p288 = .success := by decide +kernel
theorem unsat288 : Unsatisfiable (PosFin 31) f288 := by
  apply lratCheckerSound f288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p288
  · intro a ha; simp [p288] at ha; subst a; trivial
  · exact checked288
theorem derived288 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c288 := by
  apply localUnsat_implies_entails f288 [c276, c277, c60, c284, c52, c226, c259, c57, c176, c285, c287, c278, c66, c74, c78, c216, c217] c288 unsat288 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c277 := derived277 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c284 := derived284 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c259 := h 258 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  have h9 : Entails.eval a c285 := derived285 a h
  have h10 : Entails.eval a c287 := derived287 a h
  have h11 : Entails.eval a c278 := derived278 a h
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c74 := h 73 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c216 := h 215 (by decide)
  have h16 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c289 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f289 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c277, some c60, some c284, some c52, some c226, some c259, some c57, some c176, some c288, some c42, some c287, some c278, some c66, some c74, some c78, some c1, some c240, some c231, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p289 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked289 : lratChecker f289 p289 = .success := by decide +kernel
theorem unsat289 : Unsatisfiable (PosFin 31) f289 := by
  apply lratCheckerSound f289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p289
  · intro a ha; simp [p289] at ha; subst a; trivial
  · exact checked289
theorem derived289 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c289 := by
  apply localUnsat_implies_entails f289 [c276, c277, c60, c284, c52, c226, c259, c57, c176, c288, c42, c287, c278, c66, c74, c78, c1, c240, c231] c289 unsat289 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c277 := derived277 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c284 := derived284 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c259 := h 258 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  have h9 : Entails.eval a c288 := derived288 a h
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c287 := derived287 a h
  have h12 : Entails.eval a c278 := derived278 a h
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c78 := h 77 (by decide)
  have h16 : Entails.eval a c1 := h 0 (by decide)
  have h17 : Entails.eval a c240 := h 239 (by decide)
  have h18 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c290 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f290 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c289, some c62, some c276, some c284, some c52, some c225, some c226, some c259, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p290 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked290 : lratChecker f290 p290 = .success := by decide +kernel
theorem unsat290 : Unsatisfiable (PosFin 31) f290 := by
  apply lratCheckerSound f290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p290
  · intro a ha; simp [p290] at ha; subst a; trivial
  · exact checked290
theorem derived290 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c290 := by
  apply localUnsat_implies_entails f290 [c289, c62, c276, c284, c52, c225, c226, c259] c290 unsat290 (by rfl) a
  have h0 : Entails.eval a c289 := derived289 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c284 := derived284 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c225 := h 224 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c291 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨22, by decide⟩, false), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f291 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c289, some c62, some c59, some c176, some c233, some c235, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p291 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked291 : lratChecker f291 p291 = .success := by decide +kernel
theorem unsat291 : Unsatisfiable (PosFin 31) f291 := by
  apply lratCheckerSound f291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p291
  · intro a ha; simp [p291] at ha; subst a; trivial
  · exact checked291
theorem derived291 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c291 := by
  apply localUnsat_implies_entails f291 [c276, c289, c62, c59, c176, c233, c235] c291 unsat291 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c289 := derived289 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c233 := h 232 (by decide)
  have h6 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c292 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f292 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c289, some c62, some c52, some c59, some c176, some c291, some c72, some c249, some c112, some c97, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p292 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked292 : lratChecker f292 p292 = .success := by decide +kernel
theorem unsat292 : Unsatisfiable (PosFin 31) f292 := by
  apply lratCheckerSound f292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p292
  · intro a ha; simp [p292] at ha; subst a; trivial
  · exact checked292
theorem derived292 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c292 := by
  apply localUnsat_implies_entails f292 [c276, c289, c62, c52, c59, c176, c291, c72, c249, c112, c97] c292 unsat292 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c289 := derived289 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c291 := derived291 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c249 := h 248 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c293 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f293 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c289, some c62, some c52, some c59, some c176, some c292, some c49, some c65, some c84, some c72, some c77, some c97, some c105, some c7, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p293 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked293 : lratChecker f293 p293 = .success := by decide +kernel
theorem unsat293 : Unsatisfiable (PosFin 31) f293 := by
  apply lratCheckerSound f293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p293
  · intro a ha; simp [p293] at ha; subst a; trivial
  · exact checked293
theorem derived293 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c293 := by
  apply localUnsat_implies_entails f293 [c276, c289, c62, c52, c59, c176, c292, c49, c65, c84, c72, c77, c97, c105, c7] c293 unsat293 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c289 := derived289 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c292 := derived292 a h
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c97 := h 96 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c294 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f294 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c215, some c96, some c168, some c84, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p294 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked294 : lratChecker f294 p294 = .success := by decide +kernel
theorem unsat294 : Unsatisfiable (PosFin 31) f294 := by
  apply lratCheckerSound f294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p294
  · intro a ha; simp [p294] at ha; subst a; trivial
  · exact checked294
theorem derived294 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c294 := by
  apply localUnsat_implies_entails f294 [c215, c96, c168, c84] c294 unsat294 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c295 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f295 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c16, some c116, some c94, some c149, some c25, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p295 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked295 : lratChecker f295 p295 = .success := by decide +kernel
theorem unsat295 : Unsatisfiable (PosFin 31) f295 := by
  apply lratCheckerSound f295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p295
  · intro a ha; simp [p295] at ha; subst a; trivial
  · exact checked295
theorem derived295 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c295 := by
  apply localUnsat_implies_entails f295 [c16, c116, c94, c149, c25] c295 unsat295 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c296 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f296 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c149, some c14, some c98, some c257, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p296 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked296 : lratChecker f296 p296 = .success := by decide +kernel
theorem unsat296 : Unsatisfiable (PosFin 31) f296 := by
  apply lratCheckerSound f296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p296
  · intro a ha; simp [p296] at ha; subst a; trivial
  · exact checked296
theorem derived296 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c296 := by
  apply localUnsat_implies_entails f296 [c94, c149, c14, c98, c257] c296 unsat296 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c297 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f297 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c259, some c52, some c59, some c176, some c294, some c295, some c296, some c118, some c196, some c28, some c35, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p297 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked297 : lratChecker f297 p297 = .success := by decide +kernel
theorem unsat297 : Unsatisfiable (PosFin 31) f297 := by
  apply lratCheckerSound f297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p297
  · intro a ha; simp [p297] at ha; subst a; trivial
  · exact checked297
theorem derived297 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c297 := by
  apply localUnsat_implies_entails f297 [c276, c259, c52, c59, c176, c294, c295, c296, c118, c196, c28, c35] c297 unsat297 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c294 := derived294 a h
  have h6 : Entails.eval a c295 := derived295 a h
  have h7 : Entails.eval a c296 := derived296 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c298 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f298 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c196, some c237, some c271, some c35, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p298 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked298 : lratChecker f298 p298 = .success := by decide +kernel
theorem unsat298 : Unsatisfiable (PosFin 31) f298 := by
  apply lratCheckerSound f298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p298
  · intro a ha; simp [p298] at ha; subst a; trivial
  · exact checked298
theorem derived298 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c298 := by
  apply localUnsat_implies_entails f298 [c196, c237, c271, c35] c298 unsat298 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c237 := h 236 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c299 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f299 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c289, some c62, some c259, some c52, some c59, some c293, some c297, some c291, some c298, some c149, some c211, some c158, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p299 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked299 : lratChecker f299 p299 = .success := by decide +kernel
theorem unsat299 : Unsatisfiable (PosFin 31) f299 := by
  apply lratCheckerSound f299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p299
  · intro a ha; simp [p299] at ha; subst a; trivial
  · exact checked299
theorem derived299 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c299 := by
  apply localUnsat_implies_entails f299 [c276, c289, c62, c259, c52, c59, c293, c297, c291, c298, c149, c211, c158] c299 unsat299 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c289 := derived289 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c293 := derived293 a h
  have h7 : Entails.eval a c297 := derived297 a h
  have h8 : Entails.eval a c291 := derived291 a h
  have h9 : Entails.eval a c298 := derived298 a h
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c211 := h 210 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c300 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f300 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c88, some c102, some c103, some c104, some c100, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p300 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked300 : lratChecker f300 p300 = .success := by decide +kernel
theorem unsat300 : Unsatisfiable (PosFin 31) f300 := by
  apply lratCheckerSound f300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p300
  · intro a ha; simp [p300] at ha; subst a; trivial
  · exact checked300
theorem derived300 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c300 := by
  apply localUnsat_implies_entails f300 [c88, c102, c103, c104, c100] c300 unsat300 (by rfl) a
  have h0 : Entails.eval a c88 := h 87 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c301 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, false), (⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f301 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c218, some c212, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p301 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked301 : lratChecker f301 p301 = .success := by decide +kernel
theorem unsat301 : Unsatisfiable (PosFin 31) f301 := by
  apply lratCheckerSound f301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p301
  · intro a ha; simp [p301] at ha; subst a; trivial
  · exact checked301
theorem derived301 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c301 := by
  apply localUnsat_implies_entails f301 [c218, c212] c301 unsat301 (by rfl) a
  have h0 : Entails.eval a c218 := h 217 (by decide)
  have h1 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c302 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f302 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c289, some c62, some c259, some c299, some c58, some c176, some c59, some c290, some c88, some c301, some c102, some c19, some c103, some c104, some c177, some c194, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p302 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked302 : lratChecker f302 p302 = .success := by decide +kernel
theorem unsat302 : Unsatisfiable (PosFin 31) f302 := by
  apply lratCheckerSound f302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p302
  · intro a ha; simp [p302] at ha; subst a; trivial
  · exact checked302
theorem derived302 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c302 := by
  apply localUnsat_implies_entails f302 [c276, c289, c62, c259, c299, c58, c176, c59, c290, c88, c301, c102, c19, c103, c104, c177, c194] c302 unsat302 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c289 := derived289 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c299 := derived299 a h
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c290 := derived290 a h
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c301 := derived301 a h
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c104 := h 103 (by decide)
  have h15 : Entails.eval a c177 := h 176 (by decide)
  have h16 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c303 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f303 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c289, some c302, some c48, some c276, some c62, some c259, some c299, some c58, some c176, some c59, some c290, some c72, some c65, some c264, some c91, some c253, some c147, some c213, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p303 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked303 : lratChecker f303 p303 = .success := by decide +kernel
theorem unsat303 : Unsatisfiable (PosFin 31) f303 := by
  apply lratCheckerSound f303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p303
  · intro a ha; simp [p303] at ha; subst a; trivial
  · exact checked303
theorem derived303 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c303 := by
  apply localUnsat_implies_entails f303 [c289, c302, c48, c276, c62, c259, c299, c58, c176, c59, c290, c72, c65, c264, c91, c253, c147, c213] c303 unsat303 (by rfl) a
  have h0 : Entails.eval a c289 := derived289 a h
  have h1 : Entails.eval a c302 := derived302 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c276 := derived276 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c299 := derived299 a h
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c290 := derived290 a h
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c264 := h 263 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c253 := h 252 (by decide)
  have h16 : Entails.eval a c147 := h 146 (by decide)
  have h17 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c304 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f304 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c289, some c62, some c259, some c302, some c48, some c303, some c267, some c269, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p304 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked304 : lratChecker f304 p304 = .success := by decide +kernel
theorem unsat304 : Unsatisfiable (PosFin 31) f304 := by
  apply lratCheckerSound f304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p304
  · intro a ha; simp [p304] at ha; subst a; trivial
  · exact checked304
theorem derived304 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c304 := by
  apply localUnsat_implies_entails f304 [c276, c289, c62, c259, c302, c48, c303, c267, c269] c304 unsat304 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c289 := derived289 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c302 := derived302 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c303 := derived303 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c305 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f305 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c304, some c299, some c289, some c92, some c49, some c112, some c251, some c72, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p305 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked305 : lratChecker f305 p305 = .success := by decide +kernel
theorem unsat305 : Unsatisfiable (PosFin 31) f305 := by
  apply lratCheckerSound f305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p305
  · intro a ha; simp [p305] at ha; subst a; trivial
  · exact checked305
theorem derived305 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c305 := by
  apply localUnsat_implies_entails f305 [c304, c299, c289, c92, c49, c112, c251, c72] c305 unsat305 (by rfl) a
  have h0 : Entails.eval a c304 := derived304 a h
  have h1 : Entails.eval a c299 := derived299 a h
  have h2 : Entails.eval a c289 := derived289 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c306 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, true), (⟨13, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f306 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c176, some c73, some c35, some c50, some c95, some c183, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p306 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked306 : lratChecker f306 p306 = .success := by decide +kernel
theorem unsat306 : Unsatisfiable (PosFin 31) f306 := by
  apply lratCheckerSound f306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p306
  · intro a ha; simp [p306] at ha; subst a; trivial
  · exact checked306
theorem derived306 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c306 := by
  apply localUnsat_implies_entails f306 [c276, c176, c73, c35, c50, c95, c183] c306 unsat306 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c307 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f307 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c299, some c276, some c289, some c62, some c259, some c305, some c88, some c304, some c58, some c176, some c59, some c65, some c112, some c107, some c135, some c263, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p307 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked307 : lratChecker f307 p307 = .success := by decide +kernel
theorem unsat307 : Unsatisfiable (PosFin 31) f307 := by
  apply lratCheckerSound f307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p307
  · intro a ha; simp [p307] at ha; subst a; trivial
  · exact checked307
theorem derived307 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c307 := by
  apply localUnsat_implies_entails f307 [c299, c276, c289, c62, c259, c305, c88, c304, c58, c176, c59, c65, c112, c107, c135, c263] c307 unsat307 (by rfl) a
  have h0 : Entails.eval a c299 := derived299 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c289 := derived289 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c305 := derived305 a h
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c304 := derived304 a h
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c308 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f308 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c289, some c62, some c276, some c259, some c299, some c58, some c176, some c304, some c305, some c88, some c307, some c306, some c168, some c16, some c251, some c300, some c247, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p308 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked308 : lratChecker f308 p308 = .success := by decide +kernel
theorem unsat308 : Unsatisfiable (PosFin 31) f308 := by
  apply lratCheckerSound f308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p308
  · intro a ha; simp [p308] at ha; subst a; trivial
  · exact checked308
theorem derived308 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c308 := by
  apply localUnsat_implies_entails f308 [c289, c62, c276, c259, c299, c58, c176, c304, c305, c88, c307, c306, c168, c16, c251, c300, c247] c308 unsat308 (by rfl) a
  have h0 : Entails.eval a c289 := derived289 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c299 := derived299 a h
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c304 := derived304 a h
  have h8 : Entails.eval a c305 := derived305 a h
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c307 := derived307 a h
  have h11 : Entails.eval a c306 := derived306 a h
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c251 := h 250 (by decide)
  have h15 : Entails.eval a c300 := derived300 a h
  have h16 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c309 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f309 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c289, some c62, some c308, some c206, some c207, some c176, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p309 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked309 : lratChecker f309 p309 = .success := by decide +kernel
theorem unsat309 : Unsatisfiable (PosFin 31) f309 := by
  apply lratCheckerSound f309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p309
  · intro a ha; simp [p309] at ha; subst a; trivial
  · exact checked309
theorem derived309 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c309 := by
  apply localUnsat_implies_entails f309 [c276, c289, c62, c308, c206, c207, c176] c309 unsat309 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c289 := derived289 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c308 := derived308 a h
  have h4 : Entails.eval a c206 := h 205 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c310 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f310 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c309, some c62, some c206, some c225, some c53, some c175, some c56, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p310 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked310 : lratChecker f310 p310 = .success := by decide +kernel
theorem unsat310 : Unsatisfiable (PosFin 31) f310 := by
  apply lratCheckerSound f310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p310
  · intro a ha; simp [p310] at ha; subst a; trivial
  · exact checked310
theorem derived310 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c310 := by
  apply localUnsat_implies_entails f310 [c309, c62, c206, c225, c53, c175, c56] c310 unsat310 (by rfl) a
  have h0 : Entails.eval a c309 := derived309 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c311 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, true), (⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f311 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c53, some c57, some c52, some c41, some c45, some c67, some c82, some c186, some c190, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p311 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked311 : lratChecker f311 p311 = .success := by decide +kernel
theorem unsat311 : Unsatisfiable (PosFin 31) f311 := by
  apply lratCheckerSound f311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p311
  · intro a ha; simp [p311] at ha; subst a; trivial
  · exact checked311
theorem derived311 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c311 := by
  apply localUnsat_implies_entails f311 [c56, c53, c57, c52, c41, c45, c67, c82, c186, c190] c311 unsat311 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c312 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨13, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f312 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c310, some c277, some c309, some c60, some c56, some c53, some c208, some c12, some c248, some c1, some c154, some c134, some c111, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p312 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked312 : lratChecker f312 p312 = .success := by decide +kernel
theorem unsat312 : Unsatisfiable (PosFin 31) f312 := by
  apply lratCheckerSound f312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p312
  · intro a ha; simp [p312] at ha; subst a; trivial
  · exact checked312
theorem derived312 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c312 := by
  apply localUnsat_implies_entails f312 [c310, c277, c309, c60, c56, c53, c208, c12, c248, c1, c154, c134, c111] c312 unsat312 (by rfl) a
  have h0 : Entails.eval a c310 := derived310 a h
  have h1 : Entails.eval a c277 := derived277 a h
  have h2 : Entails.eval a c309 := derived309 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c134 := h 133 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c313 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f313 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c310, some c277, some c60, some c309, some c53, some c57, some c52, some c208, some c311, some c312, some c186, some c232, some c121, some c152, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p313 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked313 : lratChecker f313 p313 = .success := by decide +kernel
theorem unsat313 : Unsatisfiable (PosFin 31) f313 := by
  apply lratCheckerSound f313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p313
  · intro a ha; simp [p313] at ha; subst a; trivial
  · exact checked313
theorem derived313 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c313 := by
  apply localUnsat_implies_entails f313 [c56, c310, c277, c60, c309, c53, c57, c52, c208, c311, c312, c186, c232, c121, c152] c313 unsat313 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c310 := derived310 a h
  have h2 : Entails.eval a c277 := derived277 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c309 := derived309 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c311 := derived311 a h
  have h10 : Entails.eval a c312 := derived312 a h
  have h11 : Entails.eval a c186 := h 185 (by decide)
  have h12 : Entails.eval a c232 := h 231 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c314 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f314 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c313, some c56, some c310, some c277, some c60, some c309, some c53, some c57, some c52, some c64, some c111, some c27, some c89, some c105, some c239, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p314 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked314 : lratChecker f314 p314 = .success := by decide +kernel
theorem unsat314 : Unsatisfiable (PosFin 31) f314 := by
  apply lratCheckerSound f314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p314
  · intro a ha; simp [p314] at ha; subst a; trivial
  · exact checked314
theorem derived314 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c314 := by
  apply localUnsat_implies_entails f314 [c313, c56, c310, c277, c60, c309, c53, c57, c52, c64, c111, c27, c89, c105, c239] c314 unsat314 (by rfl) a
  have h0 : Entails.eval a c313 := derived313 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c310 := derived310 a h
  have h3 : Entails.eval a c277 := derived277 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c309 := derived309 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c315 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f315 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c310, some c277, some c60, some c309, some c56, some c53, some c208, some c313, some c42, some c312, some c314, some c72, some c77, some c1, some c223, some c222, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p315 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked315 : lratChecker f315 p315 = .success := by decide +kernel
theorem unsat315 : Unsatisfiable (PosFin 31) f315 := by
  apply lratCheckerSound f315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p315
  · intro a ha; simp [p315] at ha; subst a; trivial
  · exact checked315
theorem derived315 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c315 := by
  apply localUnsat_implies_entails f315 [c310, c277, c60, c309, c56, c53, c208, c313, c42, c312, c314, c72, c77, c1, c223, c222] c315 unsat315 (by rfl) a
  have h0 : Entails.eval a c310 := derived310 a h
  have h1 : Entails.eval a c277 := derived277 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c309 := derived309 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c313 := derived313 a h
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c312 := derived312 a h
  have h10 : Entails.eval a c314 := derived314 a h
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c77 := h 76 (by decide)
  have h13 : Entails.eval a c1 := h 0 (by decide)
  have h14 : Entails.eval a c223 := h 222 (by decide)
  have h15 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c316 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨21, by decide⟩, false), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f316 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c248, some c89, some c10, some c268, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p316 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked316 : lratChecker f316 p316 = .success := by decide +kernel
theorem unsat316 : Unsatisfiable (PosFin 31) f316 := by
  apply lratCheckerSound f316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p316
  · intro a ha; simp [p316] at ha; subst a; trivial
  · exact checked316
theorem derived316 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c316 := by
  apply localUnsat_implies_entails f316 [c248, c89, c10, c268] c316 unsat316 (by rfl) a
  have h0 : Entails.eval a c248 := h 247 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c317 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f317 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c315, some c310, some c277, some c60, some c309, some c175, some c57, some c176, some c53, some c226, some c47, some c316, some c77, some c64, some c89, some c68, some c1, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p317 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked317 : lratChecker f317 p317 = .success := by decide +kernel
theorem unsat317 : Unsatisfiable (PosFin 31) f317 := by
  apply lratCheckerSound f317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p317
  · intro a ha; simp [p317] at ha; subst a; trivial
  · exact checked317
theorem derived317 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c317 := by
  apply localUnsat_implies_entails f317 [c315, c310, c277, c60, c309, c175, c57, c176, c53, c226, c47, c316, c77, c64, c89, c68, c1] c317 unsat317 (by rfl) a
  have h0 : Entails.eval a c315 := derived315 a h
  have h1 : Entails.eval a c310 := derived310 a h
  have h2 : Entails.eval a c277 := derived277 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c309 := derived309 a h
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c176 := h 175 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c226 := h 225 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c316 := derived316 a h
  have h12 : Entails.eval a c77 := h 76 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c318 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨28, by decide⟩, false), (⟨23, by decide⟩, true), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f318 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c277, some c250, some c1, some c266, some c31, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p318 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked318 : lratChecker f318 p318 = .success := by decide +kernel
theorem unsat318 : Unsatisfiable (PosFin 31) f318 := by
  apply lratCheckerSound f318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p318
  · intro a ha; simp [p318] at ha; subst a; trivial
  · exact checked318
theorem derived318 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c318 := by
  apply localUnsat_implies_entails f318 [c277, c250, c1, c266, c31] c318 unsat318 (by rfl) a
  have h0 : Entails.eval a c277 := derived277 a h
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c319 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨28, by decide⟩, false), (⟨23, by decide⟩, true), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨26, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f319 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c53, some c87, some c277, some c318, some c45, some c39, some c108, some c195, some c229, some c252, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p319 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked319 : lratChecker f319 p319 = .success := by decide +kernel
theorem unsat319 : Unsatisfiable (PosFin 31) f319 := by
  apply lratCheckerSound f319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p319
  · intro a ha; simp [p319] at ha; subst a; trivial
  · exact checked319
theorem derived319 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c319 := by
  apply localUnsat_implies_entails f319 [c53, c87, c277, c318, c45, c39, c108, c195, c229, c252] c319 unsat319 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c277 := derived277 a h
  have h3 : Entails.eval a c318 := derived318 a h
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c320 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨28, by decide⟩, false), (⟨23, by decide⟩, true), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨26, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f320 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c53, some c87, some c319, some c10, some c102, some c128, some c117, some c178, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p320 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked320 : lratChecker f320 p320 = .success := by decide +kernel
theorem unsat320 : Unsatisfiable (PosFin 31) f320 := by
  apply lratCheckerSound f320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p320
  · intro a ha; simp [p320] at ha; subst a; trivial
  · exact checked320
theorem derived320 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c320 := by
  apply localUnsat_implies_entails f320 [c53, c87, c319, c10, c102, c128, c117, c178] c320 unsat320 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c319 := derived319 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c128 := h 127 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c321 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f321 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c309, some c310, some c277, some c60, some c315, some c175, some c226, some c57, some c53, some c176, some c317, some c87, some c320, some c169, some c268, some c262, some c107, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p321 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked321 : lratChecker f321 p321 = .success := by decide +kernel
theorem unsat321 : Unsatisfiable (PosFin 31) f321 := by
  apply lratCheckerSound f321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p321
  · intro a ha; simp [p321] at ha; subst a; trivial
  · exact checked321
theorem derived321 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c321 := by
  apply localUnsat_implies_entails f321 [c309, c310, c277, c60, c315, c175, c226, c57, c53, c176, c317, c87, c320, c169, c268, c262, c107] c321 unsat321 (by rfl) a
  have h0 : Entails.eval a c309 := derived309 a h
  have h1 : Entails.eval a c310 := derived310 a h
  have h2 : Entails.eval a c277 := derived277 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c315 := derived315 a h
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c317 := derived317 a h
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c320 := derived320 a h
  have h13 : Entails.eval a c169 := h 168 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c262 := h 261 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c322 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f322 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c321, some c309, some c60, some c242, some c208, some c226, some c53, some c175, some c58, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p322 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked322 : lratChecker f322 p322 = .success := by decide +kernel
theorem unsat322 : Unsatisfiable (PosFin 31) f322 := by
  apply lratCheckerSound f322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p322
  · intro a ha; simp [p322] at ha; subst a; trivial
  · exact checked322
theorem derived322 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c322 := by
  apply localUnsat_implies_entails f322 [c321, c309, c60, c242, c208, c226, c53, c175, c58] c322 unsat322 (by rfl) a
  have h0 : Entails.eval a c321 := derived321 a h
  have h1 : Entails.eval a c309 := derived309 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c242 := h 241 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c323 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f323 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c309, some c321, some c322, some c277, some c62, some c242, some c2, some c210, some c43, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p323 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked323 : lratChecker f323 p323 = .success := by decide +kernel
theorem unsat323 : Unsatisfiable (PosFin 31) f323 := by
  apply lratCheckerSound f323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p323
  · intro a ha; simp [p323] at ha; subst a; trivial
  · exact checked323
theorem derived323 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c323 := by
  apply localUnsat_implies_entails f323 [c309, c321, c322, c277, c62, c242, c2, c210, c43] c323 unsat323 (by rfl) a
  have h0 : Entails.eval a c309 := derived309 a h
  have h1 : Entails.eval a c321 := derived321 a h
  have h2 : Entails.eval a c322 := derived322 a h
  have h3 : Entails.eval a c277 := derived277 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c324 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f324 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c309, some c321, some c322, some c277, some c62, some c242, some c53, some c59, some c323, some c15, some c17, some c197, some c129, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p324 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked324 : lratChecker f324 p324 = .success := by decide +kernel
theorem unsat324 : Unsatisfiable (PosFin 31) f324 := by
  apply lratCheckerSound f324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p324
  · intro a ha; simp [p324] at ha; subst a; trivial
  · exact checked324
theorem derived324 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c324 := by
  apply localUnsat_implies_entails f324 [c309, c321, c322, c277, c62, c242, c53, c59, c323, c15, c17, c197, c129] c324 unsat324 (by rfl) a
  have h0 : Entails.eval a c309 := derived309 a h
  have h1 : Entails.eval a c321 := derived321 a h
  have h2 : Entails.eval a c322 := derived322 a h
  have h3 : Entails.eval a c277 := derived277 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c323 := derived323 a h
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c325 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f325 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c309, some c322, some c277, some c62, some c321, some c242, some c58, some c53, some c324, some c44, some c2, some c15, some c105, some c17, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p325 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked325 : lratChecker f325 p325 = .success := by decide +kernel
theorem unsat325 : Unsatisfiable (PosFin 31) f325 := by
  apply lratCheckerSound f325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p325
  · intro a ha; simp [p325] at ha; subst a; trivial
  · exact checked325
theorem derived325 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c325 := by
  apply localUnsat_implies_entails f325 [c309, c322, c277, c62, c321, c242, c58, c53, c324, c44, c2, c15, c105, c17] c325 unsat325 (by rfl) a
  have h0 : Entails.eval a c309 := derived309 a h
  have h1 : Entails.eval a c322 := derived322 a h
  have h2 : Entails.eval a c277 := derived277 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c321 := derived321 a h
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c324 := derived324 a h
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c326 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f326 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c309, some c321, some c322, some c277, some c62, some c242, some c58, some c53, some c59, some c52, some c325, some c34, some c33, some c27, some c77, some c154, some c6, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p326 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked326 : lratChecker f326 p326 = .success := by decide +kernel
theorem unsat326 : Unsatisfiable (PosFin 31) f326 := by
  apply lratCheckerSound f326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p326
  · intro a ha; simp [p326] at ha; subst a; trivial
  · exact checked326
theorem derived326 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c326 := by
  apply localUnsat_implies_entails f326 [c309, c321, c322, c277, c62, c242, c58, c53, c59, c52, c325, c34, c33, c27, c77, c154, c6] c326 unsat326 (by rfl) a
  have h0 : Entails.eval a c309 := derived309 a h
  have h1 : Entails.eval a c321 := derived321 a h
  have h2 : Entails.eval a c322 := derived322 a h
  have h3 : Entails.eval a c277 := derived277 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c325 := derived325 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c77 := h 76 (by decide)
  have h15 : Entails.eval a c154 := h 153 (by decide)
  have h16 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c327 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f327 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c326, some c322, some c277, some c62, some c309, some c321, some c242, some c175, some c59, some c176, some c53, some c34, some c33, some c144, some c30, some c135, some c79, some c193, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p327 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked327 : lratChecker f327 p327 = .success := by decide +kernel
theorem unsat327 : Unsatisfiable (PosFin 31) f327 := by
  apply lratCheckerSound f327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p327
  · intro a ha; simp [p327] at ha; subst a; trivial
  · exact checked327
theorem derived327 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c327 := by
  apply localUnsat_implies_entails f327 [c326, c322, c277, c62, c309, c321, c242, c175, c59, c176, c53, c34, c33, c144, c30, c135, c79, c193] c327 unsat327 (by rfl) a
  have h0 : Entails.eval a c326 := derived326 a h
  have h1 : Entails.eval a c322 := derived322 a h
  have h2 : Entails.eval a c277 := derived277 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c309 := derived309 a h
  have h5 : Entails.eval a c321 := derived321 a h
  have h6 : Entails.eval a c242 := h 241 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c144 := h 143 (by decide)
  have h14 : Entails.eval a c30 := h 29 (by decide)
  have h15 : Entails.eval a c135 := h 134 (by decide)
  have h16 : Entails.eval a c79 := h 78 (by decide)
  have h17 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c328 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f328 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c326, some c309, some c321, some c322, some c277, some c62, some c242, some c175, some c59, some c30, some c176, some c53, some c17, some c193, some c160, some c228, some c75, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p328 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked328 : lratChecker f328 p328 = .success := by decide +kernel
theorem unsat328 : Unsatisfiable (PosFin 31) f328 := by
  apply lratCheckerSound f328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p328
  · intro a ha; simp [p328] at ha; subst a; trivial
  · exact checked328
theorem derived328 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c328 := by
  apply localUnsat_implies_entails f328 [c326, c309, c321, c322, c277, c62, c242, c175, c59, c30, c176, c53, c17, c193, c160, c228, c75] c328 unsat328 (by rfl) a
  have h0 : Entails.eval a c326 := derived326 a h
  have h1 : Entails.eval a c309 := derived309 a h
  have h2 : Entails.eval a c321 := derived321 a h
  have h3 : Entails.eval a c322 := derived322 a h
  have h4 : Entails.eval a c277 := derived277 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c242 := h 241 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c228 := h 227 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c329 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f329 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c326, some c309, some c321, some c322, some c277, some c62, some c242, some c175, some c59, some c30, some c53, some c144, some c176, some c136, some c168, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p329 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked329 : lratChecker f329 p329 = .success := by decide +kernel
theorem unsat329 : Unsatisfiable (PosFin 31) f329 := by
  apply lratCheckerSound f329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p329
  · intro a ha; simp [p329] at ha; subst a; trivial
  · exact checked329
theorem derived329 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c329 := by
  apply localUnsat_implies_entails f329 [c326, c309, c321, c322, c277, c62, c242, c175, c59, c30, c53, c144, c176, c136, c168] c329 unsat329 (by rfl) a
  have h0 : Entails.eval a c326 := derived326 a h
  have h1 : Entails.eval a c309 := derived309 a h
  have h2 : Entails.eval a c321 := derived321 a h
  have h3 : Entails.eval a c322 := derived322 a h
  have h4 : Entails.eval a c277 := derived277 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c242 := h 241 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c144 := h 143 (by decide)
  have h12 : Entails.eval a c176 := h 175 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  have h14 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c330 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f330 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c309, some c322, some c277, some c62, some c321, some c242, some c326, some c175, some c59, some c53, some c144, some c30, some c329, some c328, some c114, some c162, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p330 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked330 : lratChecker f330 p330 = .success := by decide +kernel
theorem unsat330 : Unsatisfiable (PosFin 31) f330 := by
  apply lratCheckerSound f330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p330
  · intro a ha; simp [p330] at ha; subst a; trivial
  · exact checked330
theorem derived330 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c330 := by
  apply localUnsat_implies_entails f330 [c309, c322, c277, c62, c321, c242, c326, c175, c59, c53, c144, c30, c329, c328, c114, c162] c330 unsat330 (by rfl) a
  have h0 : Entails.eval a c309 := derived309 a h
  have h1 : Entails.eval a c322 := derived322 a h
  have h2 : Entails.eval a c277 := derived277 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c321 := derived321 a h
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c326 := derived326 a h
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c329 := derived329 a h
  have h13 : Entails.eval a c328 := derived328 a h
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c331 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f331 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c330, some c327, some c309, some c322, some c277, some c62, some c321, some c242, some c326, some c175, some c59, some c53, some c13, some c147, some c124, some c2, some c246, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p331 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked331 : lratChecker f331 p331 = .success := by decide +kernel
theorem unsat331 : Unsatisfiable (PosFin 31) f331 := by
  apply lratCheckerSound f331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p331
  · intro a ha; simp [p331] at ha; subst a; trivial
  · exact checked331
theorem derived331 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c331 := by
  apply localUnsat_implies_entails f331 [c330, c327, c309, c322, c277, c62, c321, c242, c326, c175, c59, c53, c13, c147, c124, c2, c246] c331 unsat331 (by rfl) a
  have h0 : Entails.eval a c330 := derived330 a h
  have h1 : Entails.eval a c327 := derived327 a h
  have h2 : Entails.eval a c309 := derived309 a h
  have h3 : Entails.eval a c322 := derived322 a h
  have h4 : Entails.eval a c277 := derived277 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c321 := derived321 a h
  have h7 : Entails.eval a c242 := h 241 (by decide)
  have h8 : Entails.eval a c326 := derived326 a h
  have h9 : Entails.eval a c175 := h 174 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c147 := h 146 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c332 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f332 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c309, some c321, some c322, some c277, some c62, some c242, some c326, some c175, some c59, some c176, some c330, some c331, some c17, some c112, some c126, some c113, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p332 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked332 : lratChecker f332 p332 = .success := by decide +kernel
theorem unsat332 : Unsatisfiable (PosFin 31) f332 := by
  apply lratCheckerSound f332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p332
  · intro a ha; simp [p332] at ha; subst a; trivial
  · exact checked332
theorem derived332 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c332 := by
  apply localUnsat_implies_entails f332 [c309, c321, c322, c277, c62, c242, c326, c175, c59, c176, c330, c331, c17, c112, c126, c113] c332 unsat332 (by rfl) a
  have h0 : Entails.eval a c309 := derived309 a h
  have h1 : Entails.eval a c321 := derived321 a h
  have h2 : Entails.eval a c322 := derived322 a h
  have h3 : Entails.eval a c277 := derived277 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c326 := derived326 a h
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c330 := derived330 a h
  have h11 : Entails.eval a c331 := derived331 a h
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c333 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f333 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c17, some c132, some c22, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p333 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked333 : lratChecker f333 p333 = .success := by decide +kernel
theorem unsat333 : Unsatisfiable (PosFin 31) f333 := by
  apply lratCheckerSound f333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p333
  · intro a ha; simp [p333] at ha; subst a; trivial
  · exact checked333
theorem derived333 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c333 := by
  apply localUnsat_implies_entails f333 [c332, c17, c132, c22] c333 unsat333 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c334 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f334 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c333, some c276, some c16, some c133, some c22, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p334 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked334 : lratChecker f334 p334 = .success := by decide +kernel
theorem unsat334 : Unsatisfiable (PosFin 31) f334 := by
  apply lratCheckerSound f334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p334
  · intro a ha; simp [p334] at ha; subst a; trivial
  · exact checked334
theorem derived334 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c334 := by
  apply localUnsat_implies_entails f334 [c332, c333, c276, c16, c133, c22] c334 unsat334 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c333 := derived333 a h
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c335 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f335 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c117, some c116, some c7, some c334, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p335 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked335 : lratChecker f335 p335 = .success := by decide +kernel
theorem unsat335 : Unsatisfiable (PosFin 31) f335 := by
  apply lratCheckerSound f335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p335
  · intro a ha; simp [p335] at ha; subst a; trivial
  · exact checked335
theorem derived335 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c335 := by
  apply localUnsat_implies_entails f335 [c117, c116, c7, c334] c335 unsat335 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c334 := derived334 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c336 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f336 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c164, some c106, some c22, some c4, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p336 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked336 : lratChecker f336 p336 = .success := by decide +kernel
theorem unsat336 : Unsatisfiable (PosFin 31) f336 := by
  apply lratCheckerSound f336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p336
  · intro a ha; simp [p336] at ha; subst a; trivial
  · exact checked336
theorem derived336 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c336 := by
  apply localUnsat_implies_entails f336 [c164, c106, c22, c4] c336 unsat336 (by rfl) a
  have h0 : Entails.eval a c164 := h 163 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c337 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f337 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c1, some c7, some c336, some c133, some c276, some c132, some c18, some c131, some c3, some c165, some c39, some c273, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p337 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked337 : lratChecker f337 p337 = .success := by decide +kernel
theorem unsat337 : Unsatisfiable (PosFin 31) f337 := by
  apply lratCheckerSound f337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p337
  · intro a ha; simp [p337] at ha; subst a; trivial
  · exact checked337
theorem derived337 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c337 := by
  apply localUnsat_implies_entails f337 [c332, c1, c7, c336, c133, c276, c132, c18, c131, c3, c165, c39, c273] c337 unsat337 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c336 := derived336 a h
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c276 := derived276 a h
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c338 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f338 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c37, some c80, some c3, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p338 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked338 : lratChecker f338 p338 = .success := by decide +kernel
theorem unsat338 : Unsatisfiable (PosFin 31) f338 := by
  apply lratCheckerSound f338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p338
  · intro a ha; simp [p338] at ha; subst a; trivial
  · exact checked338
theorem derived338 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c338 := by
  apply localUnsat_implies_entails f338 [c37, c80, c3] c338 unsat338 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c339 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f339 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c335, some c338, some c337, some c35, some c76, some c3, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p339 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked339 : lratChecker f339 p339 = .success := by decide +kernel
theorem unsat339 : Unsatisfiable (PosFin 31) f339 := by
  apply lratCheckerSound f339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p339
  · intro a ha; simp [p339] at ha; subst a; trivial
  · exact checked339
theorem derived339 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c339 := by
  apply localUnsat_implies_entails f339 [c335, c338, c337, c35, c76, c3] c339 unsat339 (by rfl) a
  have h0 : Entails.eval a c335 := derived335 a h
  have h1 : Entails.eval a c338 := derived338 a h
  have h2 : Entails.eval a c337 := derived337 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c340 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f340 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c35, some c116, some c76, some c3, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p340 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked340 : lratChecker f340 p340 = .success := by decide +kernel
theorem unsat340 : Unsatisfiable (PosFin 31) f340 := by
  apply lratCheckerSound f340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p340
  · intro a ha; simp [p340] at ha; subst a; trivial
  · exact checked340
theorem derived340 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c340 := by
  apply localUnsat_implies_entails f340 [c35, c116, c76, c3] c340 unsat340 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c341 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f341 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c3, some c8, some c270, some c272, some c20, some c167, some c140, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p341 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked341 : lratChecker f341 p341 = .success := by decide +kernel
theorem unsat341 : Unsatisfiable (PosFin 31) f341 := by
  apply lratCheckerSound f341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p341
  · intro a ha; simp [p341] at ha; subst a; trivial
  · exact checked341
theorem derived341 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c341 := by
  apply localUnsat_implies_entails f341 [c3, c8, c270, c272, c20, c167, c140] c341 unsat341 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c342 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f342 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c340, some c339, some c338, some c341, some c145, some c26, some c146, some c115, some c2, some c81, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p342 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked342 : lratChecker f342 p342 = .success := by decide +kernel
theorem unsat342 : Unsatisfiable (PosFin 31) f342 := by
  apply lratCheckerSound f342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p342
  · intro a ha; simp [p342] at ha; subst a; trivial
  · exact checked342
theorem derived342 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c342 := by
  apply localUnsat_implies_entails f342 [c340, c339, c338, c341, c145, c26, c146, c115, c2, c81] c342 unsat342 (by rfl) a
  have h0 : Entails.eval a c340 := derived340 a h
  have h1 : Entails.eval a c339 := derived339 a h
  have h2 : Entails.eval a c338 := derived338 a h
  have h3 : Entails.eval a c341 := derived341 a h
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c343 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨14, by decide⟩, false), (⟨2, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f343 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c115, some c81, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p343 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked343 : lratChecker f343 p343 = .success := by decide +kernel
theorem unsat343 : Unsatisfiable (PosFin 31) f343 := by
  apply lratCheckerSound f343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p343
  · intro a ha; simp [p343] at ha; subst a; trivial
  · exact checked343
theorem derived343 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c343 := by
  apply localUnsat_implies_entails f343 [c115, c81] c343 unsat343 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c344 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f344 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c339, some c340, some c342, some c117, some c334, some c2, some c343, some c8, some c20, some c17, some c133, some c276, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p344 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked344 : lratChecker f344 p344 = .success := by decide +kernel
theorem unsat344 : Unsatisfiable (PosFin 31) f344 := by
  apply lratCheckerSound f344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p344
  · intro a ha; simp [p344] at ha; subst a; trivial
  · exact checked344
theorem derived344 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c344 := by
  apply localUnsat_implies_entails f344 [c332, c339, c340, c342, c117, c334, c2, c343, c8, c20, c17, c133, c276] c344 unsat344 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c339 := derived339 a h
  have h2 : Entails.eval a c340 := derived340 a h
  have h3 : Entails.eval a c342 := derived342 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c334 := derived334 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c343 := derived343 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c276 := derived276 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c345 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f345 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c138, some c18, some c276, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p345 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked345 : lratChecker f345 p345 = .success := by decide +kernel
theorem unsat345 : Unsatisfiable (PosFin 31) f345 := by
  apply lratCheckerSound f345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p345
  · intro a ha; simp [p345] at ha; subst a; trivial
  · exact checked345
theorem derived345 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c345 := by
  apply localUnsat_implies_entails f345 [c332, c138, c18, c276] c345 unsat345 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c276 := derived276 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c346 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f346 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c159, some c101, some c20, some c4, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p346 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked346 : lratChecker f346 p346 = .success := by decide +kernel
theorem unsat346 : Unsatisfiable (PosFin 31) f346 := by
  apply lratCheckerSound f346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p346
  · intro a ha; simp [p346] at ha; subst a; trivial
  · exact checked346
theorem derived346 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c346 := by
  apply localUnsat_implies_entails f346 [c159, c101, c20, c4] c346 unsat346 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c347 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f347 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c19, some c345, some c346, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p347 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked347 : lratChecker f347 p347 = .success := by decide +kernel
theorem unsat347 : Unsatisfiable (PosFin 31) f347 := by
  apply lratCheckerSound f347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p347
  · intro a ha; simp [p347] at ha; subst a; trivial
  · exact checked347
theorem derived347 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c347 := by
  apply localUnsat_implies_entails f347 [c19, c345, c346] c347 unsat347 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c345 := derived345 a h
  have h2 : Entails.eval a c346 := derived346 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c348 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f348 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c347, some c7, some c21, some c336, some c345, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p348 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked348 : lratChecker f348 p348 = .success := by decide +kernel
theorem unsat348 : Unsatisfiable (PosFin 31) f348 := by
  apply lratCheckerSound f348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p348
  · intro a ha; simp [p348] at ha; subst a; trivial
  · exact checked348
theorem derived348 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c348 := by
  apply localUnsat_implies_entails f348 [c347, c7, c21, c336, c345] c348 unsat348 (by rfl) a
  have h0 : Entails.eval a c347 := derived347 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c336 := derived336 a h
  have h4 : Entails.eval a c345 := derived345 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c349 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f349 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c53, some c173, some c276, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p349 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked349 : lratChecker f349 p349 = .success := by decide +kernel
theorem unsat349 : Unsatisfiable (PosFin 31) f349 := by
  apply lratCheckerSound f349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p349
  · intro a ha; simp [p349] at ha; subst a; trivial
  · exact checked349
theorem derived349 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c349 := by
  apply localUnsat_implies_entails f349 [c332, c53, c173, c276] c349 unsat349 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c276 := derived276 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c350 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f350 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c139, some c157, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p350 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked350 : lratChecker f350 p350 = .success := by decide +kernel
theorem unsat350 : Unsatisfiable (PosFin 31) f350 := by
  apply lratCheckerSound f350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p350
  · intro a ha; simp [p350] at ha; subst a; trivial
  · exact checked350
theorem derived350 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c350 := by
  apply localUnsat_implies_entails f350 [c139, c157] c350 unsat350 (by rfl) a
  have h0 : Entails.eval a c139 := h 138 (by decide)
  have h1 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c351 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f351 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c344, some c348, some c148, some c349, some c350, some c37, some c27, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p351 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked351 : lratChecker f351 p351 = .success := by decide +kernel
theorem unsat351 : Unsatisfiable (PosFin 31) f351 := by
  apply lratCheckerSound f351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p351
  · intro a ha; simp [p351] at ha; subst a; trivial
  · exact checked351
theorem derived351 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c351 := by
  apply localUnsat_implies_entails f351 [c344, c348, c148, c349, c350, c37, c27] c351 unsat351 (by rfl) a
  have h0 : Entails.eval a c344 := derived344 a h
  have h1 : Entails.eval a c348 := derived348 a h
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c349 := derived349 a h
  have h4 : Entails.eval a c350 := derived350 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c352 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f352 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c351, some c344, some c148, some c37, some c80, some c27, some c23, some c350, some c173, some c28, some c79, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p352 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked352 : lratChecker f352 p352 = .success := by decide +kernel
theorem unsat352 : Unsatisfiable (PosFin 31) f352 := by
  apply lratCheckerSound f352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p352
  · intro a ha; simp [p352] at ha; subst a; trivial
  · exact checked352
theorem derived352 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c352 := by
  apply localUnsat_implies_entails f352 [c332, c351, c344, c148, c37, c80, c27, c23, c350, c173, c28, c79] c352 unsat352 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c351 := derived351 a h
  have h2 : Entails.eval a c344 := derived344 a h
  have h3 : Entails.eval a c148 := h 147 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c350 := derived350 a h
  have h9 : Entails.eval a c173 := h 172 (by decide)
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c353 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f353 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c238, some c234, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p353 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked353 : lratChecker f353 p353 = .success := by decide +kernel
theorem unsat353 : Unsatisfiable (PosFin 31) f353 := by
  apply lratCheckerSound f353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p353
  · intro a ha; simp [p353] at ha; subst a; trivial
  · exact checked353
theorem derived353 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c353 := by
  apply localUnsat_implies_entails f353 [c332, c238, c234] c353 unsat353 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c238 := h 237 (by decide)
  have h2 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c354 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f354 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c173, some c276, some c172, some c55, some c353, some c199, some c202, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p354 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked354 : lratChecker f354 p354 = .success := by decide +kernel
theorem unsat354 : Unsatisfiable (PosFin 31) f354 := by
  apply lratCheckerSound f354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p354
  · intro a ha; simp [p354] at ha; subst a; trivial
  · exact checked354
theorem derived354 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c354 := by
  apply localUnsat_implies_entails f354 [c332, c173, c276, c172, c55, c353, c199, c202] c354 unsat354 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c173 := h 172 (by decide)
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c353 := derived353 a h
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c355 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f355 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c57, some c59, some c26, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p355 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked355 : lratChecker f355 p355 = .success := by decide +kernel
theorem unsat355 : Unsatisfiable (PosFin 31) f355 := by
  apply lratCheckerSound f355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p355
  · intro a ha; simp [p355] at ha; subst a; trivial
  · exact checked355
theorem derived355 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c355 := by
  apply localUnsat_implies_entails f355 [c57, c59, c26] c355 unsat355 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c356 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f356 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c354, some c355, some c172, some c276, some c54, some c224, some c169, some c141, some c219, some c220, some c171, some c201, some c110, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p356 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked356 : lratChecker f356 p356 = .success := by decide +kernel
theorem unsat356 : Unsatisfiable (PosFin 31) f356 := by
  apply lratCheckerSound f356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p356
  · intro a ha; simp [p356] at ha; subst a; trivial
  · exact checked356
theorem derived356 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c356 := by
  apply localUnsat_implies_entails f356 [c332, c354, c355, c172, c276, c54, c224, c169, c141, c219, c220, c171, c201, c110] c356 unsat356 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c354 := derived354 a h
  have h2 : Entails.eval a c355 := derived355 a h
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c276 := derived276 a h
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c224 := h 223 (by decide)
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c171 := h 170 (by decide)
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c357 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f357 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c352, some c344, some c354, some c355, some c27, some c356, some c146, some c2, some c343, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p357 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked357 : lratChecker f357 p357 = .success := by decide +kernel
theorem unsat357 : Unsatisfiable (PosFin 31) f357 := by
  apply lratCheckerSound f357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p357
  · intro a ha; simp [p357] at ha; subst a; trivial
  · exact checked357
theorem derived357 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c357 := by
  apply localUnsat_implies_entails f357 [c352, c344, c354, c355, c27, c356, c146, c2, c343] c357 unsat357 (by rfl) a
  have h0 : Entails.eval a c352 := derived352 a h
  have h1 : Entails.eval a c344 := derived344 a h
  have h2 : Entails.eval a c354 := derived354 a h
  have h3 : Entails.eval a c355 := derived355 a h
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c356 := derived356 a h
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c343 := derived343 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c358 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f358 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c13, some c142, some c58, some c7, some c20, some c99, some c214, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p358 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked358 : lratChecker f358 p358 = .success := by decide +kernel
theorem unsat358 : Unsatisfiable (PosFin 31) f358 := by
  apply lratCheckerSound f358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p358
  · intro a ha; simp [p358] at ha; subst a; trivial
  · exact checked358
theorem derived358 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c358 := by
  apply localUnsat_implies_entails f358 [c332, c13, c142, c58, c7, c20, c99, c214] c358 unsat358 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c359 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨10, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f359 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c358, some c26, some c169, some c219, some c87, some c93, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p359 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked359 : lratChecker f359 p359 = .success := by decide +kernel
theorem unsat359 : Unsatisfiable (PosFin 31) f359 := by
  apply lratCheckerSound f359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p359
  · intro a ha; simp [p359] at ha; subst a; trivial
  · exact checked359
theorem derived359 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c359 := by
  apply localUnsat_implies_entails f359 [c332, c358, c26, c169, c219, c87, c93] c359 unsat359 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c358 := derived358 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c169 := h 168 (by decide)
  have h4 : Entails.eval a c219 := h 218 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c360 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f360 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c26, some c169, some c10, some c87, some c1, some c92, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p360 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked360 : lratChecker f360 p360 = .success := by decide +kernel
theorem unsat360 : Unsatisfiable (PosFin 31) f360 := by
  apply lratCheckerSound f360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p360
  · intro a ha; simp [p360] at ha; subst a; trivial
  · exact checked360
theorem derived360 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c360 := by
  apply localUnsat_implies_entails f360 [c26, c169, c10, c87, c1, c92] c360 unsat360 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c361 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f361 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c344, some c352, some c357, some c359, some c360, some c13, some c58, some c2, some c7, some c55, some c343, some c346, some c254, some c184, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p361 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked361 : lratChecker f361 p361 = .success := by decide +kernel
theorem unsat361 : Unsatisfiable (PosFin 31) f361 := by
  apply lratCheckerSound f361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p361
  · intro a ha; simp [p361] at ha; subst a; trivial
  · exact checked361
theorem derived361 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c361 := by
  apply localUnsat_implies_entails f361 [c332, c344, c352, c357, c359, c360, c13, c58, c2, c7, c55, c343, c346, c254, c184] c361 unsat361 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c344 := derived344 a h
  have h2 : Entails.eval a c352 := derived352 a h
  have h3 : Entails.eval a c357 := derived357 a h
  have h4 : Entails.eval a c359 := derived359 a h
  have h5 : Entails.eval a c360 := derived360 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c343 := derived343 a h
  have h12 : Entails.eval a c346 := derived346 a h
  have h13 : Entails.eval a c254 := h 253 (by decide)
  have h14 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c362 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f362 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c344, some c361, some c147, some c35, some c349, some c173, some c28, some c76, some c75, some c23, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p362 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked362 : lratChecker f362 p362 = .success := by decide +kernel
theorem unsat362 : Unsatisfiable (PosFin 31) f362 := by
  apply lratCheckerSound f362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p362
  · intro a ha; simp [p362] at ha; subst a; trivial
  · exact checked362
theorem derived362 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c362 := by
  apply localUnsat_implies_entails f362 [c332, c344, c361, c147, c35, c349, c173, c28, c76, c75, c23] c362 unsat362 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c344 := derived344 a h
  have h2 : Entails.eval a c361 := derived361 a h
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c349 := derived349 a h
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c363 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f363 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c205, some c224, some c276, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p363 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked363 : lratChecker f363 p363 = .success := by decide +kernel
theorem unsat363 : Unsatisfiable (PosFin 31) f363 := by
  apply lratCheckerSound f363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p363
  · intro a ha; simp [p363] at ha; subst a; trivial
  · exact checked363
theorem derived363 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c363 := by
  apply localUnsat_implies_entails f363 [c332, c205, c224, c276] c363 unsat363 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c224 := h 223 (by decide)
  have h3 : Entails.eval a c276 := derived276 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c364 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f364 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c57, some c59, some c363, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p364 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked364 : lratChecker f364 p364 = .success := by decide +kernel
theorem unsat364 : Unsatisfiable (PosFin 31) f364 := by
  apply lratCheckerSound f364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p364
  · intro a ha; simp [p364] at ha; subst a; trivial
  · exact checked364
theorem derived364 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c364 := by
  apply localUnsat_implies_entails f364 [c57, c59, c363] c364 unsat364 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c363 := derived363 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c365 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f365 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c344, some c361, some c35, some c147, some c27, some c362, some c364, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p365 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked365 : lratChecker f365 p365 = .success := by decide +kernel
theorem unsat365 : Unsatisfiable (PosFin 31) f365 := by
  apply lratCheckerSound f365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p365
  · intro a ha; simp [p365] at ha; subst a; trivial
  · exact checked365
theorem derived365 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c365 := by
  apply localUnsat_implies_entails f365 [c344, c361, c35, c147, c27, c362, c364] c365 unsat365 (by rfl) a
  have h0 : Entails.eval a c344 := derived344 a h
  have h1 : Entails.eval a c361 := derived361 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c362 := derived362 a h
  have h6 : Entails.eval a c364 := derived364 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c366 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f366 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c364, some c172, some c276, some c365, some c35, some c151, some c74, some c182, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p366 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked366 : lratChecker f366 p366 = .success := by decide +kernel
theorem unsat366 : Unsatisfiable (PosFin 31) f366 := by
  apply lratCheckerSound f366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p366
  · intro a ha; simp [p366] at ha; subst a; trivial
  · exact checked366
theorem derived366 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c366 := by
  apply localUnsat_implies_entails f366 [c332, c364, c172, c276, c365, c35, c151, c74, c182] c366 unsat366 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c364 := derived364 a h
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c276 := derived276 a h
  have h4 : Entails.eval a c365 := derived365 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c151 := h 150 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c367 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f367 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c364, some c276, some c54, some c78, some c220, some c217, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p367 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked367 : lratChecker f367 p367 = .success := by decide +kernel
theorem unsat367 : Unsatisfiable (PosFin 31) f367 := by
  apply lratCheckerSound f367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p367
  · intro a ha; simp [p367] at ha; subst a; trivial
  · exact checked367
theorem derived367 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c367 := by
  apply localUnsat_implies_entails f367 [c332, c364, c276, c54, c78, c220, c217] c367 unsat367 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c364 := derived364 a h
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c220 := h 219 (by decide)
  have h6 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c368 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f368 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c364, some c172, some c367, some c276, some c52, some c182, some c152, some c255, some c188, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p368 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked368 : lratChecker f368 p368 = .success := by decide +kernel
theorem unsat368 : Unsatisfiable (PosFin 31) f368 := by
  apply lratCheckerSound f368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p368
  · intro a ha; simp [p368] at ha; subst a; trivial
  · exact checked368
theorem derived368 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c368 := by
  apply localUnsat_implies_entails f368 [c332, c364, c172, c367, c276, c52, c182, c152, c255, c188] c368 unsat368 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c364 := derived364 a h
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c367 := derived367 a h
  have h4 : Entails.eval a c276 := derived276 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c182 := h 181 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c369 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f369 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c364, some c365, some c172, some c276, some c52, some c366, some c367, some c368, some c185, some c37, some c255, some c71, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p369 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked369 : lratChecker f369 p369 = .success := by decide +kernel
theorem unsat369 : Unsatisfiable (PosFin 31) f369 := by
  apply lratCheckerSound f369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p369
  · intro a ha; simp [p369] at ha; subst a; trivial
  · exact checked369
theorem derived369 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c369 := by
  apply localUnsat_implies_entails f369 [c332, c364, c365, c172, c276, c52, c366, c367, c368, c185, c37, c255, c71] c369 unsat369 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c364 := derived364 a h
  have h2 : Entails.eval a c365 := derived365 a h
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c276 := derived276 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c366 := derived366 a h
  have h7 : Entails.eval a c367 := derived367 a h
  have h8 : Entails.eval a c368 := derived368 a h
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c255 := h 254 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c370 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f370 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c58, some c26, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p370 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked370 : lratChecker f370 p370 = .success := by decide +kernel
theorem unsat370 : Unsatisfiable (PosFin 31) f370 := by
  apply lratCheckerSound f370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p370
  · intro a ha; simp [p370] at ha; subst a; trivial
  · exact checked370
theorem derived370 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c370 := by
  apply localUnsat_implies_entails f370 [c56, c58, c26] c370 unsat370 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c371 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f371 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c364, some c369, some c37, some c370, some c54, some c276, some c175, some c365, some c26, some c360, some c243, some c167, some c115, some c130, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p371 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked371 : lratChecker f371 p371 = .success := by decide +kernel
theorem unsat371 : Unsatisfiable (PosFin 31) f371 := by
  apply lratCheckerSound f371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p371
  · intro a ha; simp [p371] at ha; subst a; trivial
  · exact checked371
theorem derived371 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c371 := by
  apply localUnsat_implies_entails f371 [c332, c364, c369, c37, c370, c54, c276, c175, c365, c26, c360, c243, c167, c115, c130] c371 unsat371 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c364 := derived364 a h
  have h2 : Entails.eval a c369 := derived369 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c370 := derived370 a h
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c276 := derived276 a h
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c365 := derived365 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c360 := derived360 a h
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c372 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f372 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c37, some c371, some c146, some c2, some c343, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p372 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked372 : lratChecker f372 p372 = .success := by decide +kernel
theorem unsat372 : Unsatisfiable (PosFin 31) f372 := by
  apply lratCheckerSound f372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p372
  · intro a ha; simp [p372] at ha; subst a; trivial
  · exact checked372
theorem derived372 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c372 := by
  apply localUnsat_implies_entails f372 [c37, c371, c146, c2, c343] c372 unsat372 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c371 := derived371 a h
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c343 := derived343 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c373 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f373 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c276, some c2, some c7, some c241, some c125, some c18, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p373 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked373 : lratChecker f373 p373 = .success := by decide +kernel
theorem unsat373 : Unsatisfiable (PosFin 31) f373 := by
  apply lratCheckerSound f373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p373
  · intro a ha; simp [p373] at ha; subst a; trivial
  · exact checked373
theorem derived373 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c373 := by
  apply localUnsat_implies_entails f373 [c332, c276, c2, c7, c241, c125, c18] c373 unsat373 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived373

end CochromaticTwenty.Certificates.Z12Direct_5_4_11
