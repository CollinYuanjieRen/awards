import MerLeanExperiment.Certificates.Z12Direct_4_3_7.Inputs

/-! Generated from the actual pinned z12direct_4_3_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c58 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f58 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c8, some c31, some c24, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p58 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked58 : lratChecker f58 p58 = .success := by decide +kernel
theorem unsat58 : Unsatisfiable (PosFin 29) f58 := by
  apply lratCheckerSound f58 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p58
  · intro a ha; simp [p58] at ha; subst a; trivial
  · exact checked58
theorem derived58 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c58 := by
  apply localUnsat_implies_entails f58 [c8, c31, c24] c58 unsat58 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c59 : DefaultClause 29 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f59 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c14, some c32, some c25, some c58, some c13, some c10, some c18, some c50, some c55, some c22, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p59 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked59 : lratChecker f59 p59 = .success := by decide +kernel
theorem unsat59 : Unsatisfiable (PosFin 29) f59 := by
  apply lratCheckerSound f59 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p59
  · intro a ha; simp [p59] at ha; subst a; trivial
  · exact checked59
theorem derived59 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c59 := by
  apply localUnsat_implies_entails f59 [c14, c32, c25, c58, c13, c10, c18, c50, c55, c22] c59 unsat59 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c58 := derived58 a h
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c60 : DefaultClause 29 := directClause [(⟨4, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f60 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c32, some c25, some c58, some c5, some c37, some c30, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p60 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked60 : lratChecker f60 p60 = .success := by decide +kernel
theorem unsat60 : Unsatisfiable (PosFin 29) f60 := by
  apply lratCheckerSound f60 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p60
  · intro a ha; simp [p60] at ha; subst a; trivial
  · exact checked60
theorem derived60 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c60 := by
  apply localUnsat_implies_entails f60 [c32, c25, c58, c5, c37, c30] c60 unsat60 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c58 := derived58 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c61 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f61 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c14, some c32, some c25, some c58, some c13, some c60, some c41, some c10, some c11, some c59, some c50, some c44, some c6, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p61 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked61 : lratChecker f61 p61 = .success := by decide +kernel
theorem unsat61 : Unsatisfiable (PosFin 29) f61 := by
  apply lratCheckerSound f61 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p61
  · intro a ha; simp [p61] at ha; subst a; trivial
  · exact checked61
theorem derived61 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c61 := by
  apply localUnsat_implies_entails f61 [c14, c32, c25, c58, c13, c60, c41, c10, c11, c59, c50, c44, c6] c61 unsat61 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c58 := derived58 a h
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c60 := derived60 a h
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c59 := derived59 a h
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c62 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f62 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c13, some c32, some c30, some c22, some c36, some c55, some c34, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p62 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked62 : lratChecker f62 p62 = .success := by decide +kernel
theorem unsat62 : Unsatisfiable (PosFin 29) f62 := by
  apply lratCheckerSound f62 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p62
  · intro a ha; simp [p62] at ha; subst a; trivial
  · exact checked62
theorem derived62 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c62 := by
  apply localUnsat_implies_entails f62 [c13, c32, c30, c22, c36, c55, c34] c62 unsat62 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c63 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f63 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c32, some c58, some c60, some c13, some c62, some c12, some c15, some c19, some c17, some c50, some c45, some c56, some c53, some c29, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p63 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked63 : lratChecker f63 p63 = .success := by decide +kernel
theorem unsat63 : Unsatisfiable (PosFin 29) f63 := by
  apply lratCheckerSound f63 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p63
  · intro a ha; simp [p63] at ha; subst a; trivial
  · exact checked63
theorem derived63 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c63 := by
  apply localUnsat_implies_entails f63 [c61, c32, c58, c60, c13, c62, c12, c15, c19, c17, c50, c45, c56, c53, c29] c63 unsat63 (by rfl) a
  have h0 : Entails.eval a c61 := derived61 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c58 := derived58 a h
  have h3 : Entails.eval a c60 := derived60 a h
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c62 := derived62 a h
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c64 : DefaultClause 29 := directClause [(⟨4, by decide⟩, true), (⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f64 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c45, some c57, some c52, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p64 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked64 : lratChecker f64 p64 = .success := by decide +kernel
theorem unsat64 : Unsatisfiable (PosFin 29) f64 := by
  apply lratCheckerSound f64 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p64
  · intro a ha; simp [p64] at ha; subst a; trivial
  · exact checked64
theorem derived64 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c64 := by
  apply localUnsat_implies_entails f64 [c45, c57, c52] c64 unsat64 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c65 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false), (⟨24, by decide⟩, true), (⟨26, by decide⟩, false), (⟨8, by decide⟩, false), (⟨27, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f65 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c63, some c21, some c20, some c16, some c15, some c12, some c22, some c64, some c5, some c47, some c48, some c3, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p65 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked65 : lratChecker f65 p65 = .success := by decide +kernel
theorem unsat65 : Unsatisfiable (PosFin 29) f65 := by
  apply lratCheckerSound f65 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p65
  · intro a ha; simp [p65] at ha; subst a; trivial
  · exact checked65
theorem derived65 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c65 := by
  apply localUnsat_implies_entails f65 [c61, c63, c21, c20, c16, c15, c12, c22, c64, c5, c47, c48, c3] c65 unsat65 (by rfl) a
  have h0 : Entails.eval a c61 := derived61 a h
  have h1 : Entails.eval a c63 := derived63 a h
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c64 := derived64 a h
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c66 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f66 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c13, some c12, some c15, some c16, some c19, some c17, some c65, some c2, some c46, some c23, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p66 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked66 : lratChecker f66 p66 = .success := by decide +kernel
theorem unsat66 : Unsatisfiable (PosFin 29) f66 := by
  apply lratCheckerSound f66 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p66
  · intro a ha; simp [p66] at ha; subst a; trivial
  · exact checked66
theorem derived66 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c66 := by
  apply localUnsat_implies_entails f66 [c61, c13, c12, c15, c16, c19, c17, c65, c2, c46, c23] c66 unsat66 (by rfl) a
  have h0 : Entails.eval a c61 := derived61 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c65 := derived65 a h
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c67 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f67 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c63, some c13, some c66, some c30, some c22, some c55, some c51, some c6, some c33, some c5, some c36, some c1, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p67 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked67 : lratChecker f67 p67 = .success := by decide +kernel
theorem unsat67 : Unsatisfiable (PosFin 29) f67 := by
  apply lratCheckerSound f67 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p67
  · intro a ha; simp [p67] at ha; subst a; trivial
  · exact checked67
theorem derived67 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c67 := by
  apply localUnsat_implies_entails f67 [c61, c63, c13, c66, c30, c22, c55, c51, c6, c33, c5, c36, c1] c67 unsat67 (by rfl) a
  have h0 : Entails.eval a c61 := derived61 a h
  have h1 : Entails.eval a c63 := derived63 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c66 := derived66 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c68 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f68 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c67, some c31, some c63, some c30, some c22, some c33, some c51, some c35, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p68 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked68 : lratChecker f68 p68 = .success := by decide +kernel
theorem unsat68 : Unsatisfiable (PosFin 29) f68 := by
  apply lratCheckerSound f68 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p68
  · intro a ha; simp [p68] at ha; subst a; trivial
  · exact checked68
theorem derived68 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c68 := by
  apply localUnsat_implies_entails f68 [c61, c67, c31, c63, c30, c22, c33, c51, c35] c68 unsat68 (by rfl) a
  have h0 : Entails.eval a c61 := derived61 a h
  have h1 : Entails.eval a c67 := derived67 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c63 := derived63 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c69 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f69 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c63, some c67, some c31, some c24, some c68, some c12, some c9, some c38, some c54, some c35, some c42, some c22, some c28, some c26, some c43, some c49, some c65, some c40, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p69 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked69 : lratChecker f69 p69 = .success := by decide +kernel
theorem unsat69 : Unsatisfiable (PosFin 29) f69 := by
  apply lratCheckerSound f69 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p69
  · intro a ha; simp [p69] at ha; subst a; trivial
  · exact checked69
theorem derived69 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c69 := by
  apply localUnsat_implies_entails f69 [c61, c63, c67, c31, c24, c68, c12, c9, c38, c54, c35, c42, c22, c28, c26, c43, c49, c65, c40] c69 unsat69 (by rfl) a
  have h0 : Entails.eval a c61 := derived61 a h
  have h1 : Entails.eval a c63 := derived63 a h
  have h2 : Entails.eval a c67 := derived67 a h
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c68 := derived68 a h
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c43 := h 42 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c65 := derived65 a h
  have h18 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c70 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f70 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c69, some c25, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p70 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked70 : lratChecker f70 p70 = .success := by decide +kernel
theorem unsat70 : Unsatisfiable (PosFin 29) f70 := by
  apply lratCheckerSound f70 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p70
  · intro a ha; simp [p70] at ha; subst a; trivial
  · exact checked70
theorem derived70 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c70 := by
  apply localUnsat_implies_entails f70 [c69, c25] c70 unsat70 (by rfl) a
  have h0 : Entails.eval a c69 := derived69 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c71 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f71 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c70, some c32, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p71 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked71 : lratChecker f71 p71 = .success := by decide +kernel
theorem unsat71 : Unsatisfiable (PosFin 29) f71 := by
  apply lratCheckerSound f71 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p71
  · intro a ha; simp [p71] at ha; subst a; trivial
  · exact checked71
theorem derived71 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c71 := by
  apply localUnsat_implies_entails f71 [c70, c32] c71 unsat71 (by rfl) a
  have h0 : Entails.eval a c70 := derived70 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c72 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f72 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c71, some c69, some c31, some c24, some c12, some c9, some c54, some c7, some c27, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p72 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked72 : lratChecker f72 p72 = .success := by decide +kernel
theorem unsat72 : Unsatisfiable (PosFin 29) f72 := by
  apply lratCheckerSound f72 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p72
  · intro a ha; simp [p72] at ha; subst a; trivial
  · exact checked72
theorem derived72 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c72 := by
  apply localUnsat_implies_entails f72 [c71, c69, c31, c24, c12, c9, c54, c7, c27] c72 unsat72 (by rfl) a
  have h0 : Entails.eval a c71 := derived71 a h
  have h1 : Entails.eval a c69 := derived69 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c73 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f73 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c70, some c61, some c30, some c51, some c22, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p73 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked73 : lratChecker f73 p73 = .success := by decide +kernel
theorem unsat73 : Unsatisfiable (PosFin 29) f73 := by
  apply lratCheckerSound f73 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p73
  · intro a ha; simp [p73] at ha; subst a; trivial
  · exact checked73
theorem derived73 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c73 := by
  apply localUnsat_implies_entails f73 [c70, c61, c30, c51, c22] c73 unsat73 (by rfl) a
  have h0 : Entails.eval a c70 := derived70 a h
  have h1 : Entails.eval a c61 := derived61 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c74 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f74 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c73, some c72, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p74 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked74 : lratChecker f74 p74 = .success := by decide +kernel
theorem unsat74 : Unsatisfiable (PosFin 29) f74 := by
  apply lratCheckerSound f74 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p74
  · intro a ha; simp [p74] at ha; subst a; trivial
  · exact checked74
theorem derived74 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c74 := by
  apply localUnsat_implies_entails f74 [c73, c72] c74 unsat74 (by rfl) a
  have h0 : Entails.eval a c73 := derived73 a h
  have h1 : Entails.eval a c72 := derived72 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c75 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f75 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c74, some c13, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p75 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked75 : lratChecker f75 p75 = .success := by decide +kernel
theorem unsat75 : Unsatisfiable (PosFin 29) f75 := by
  apply lratCheckerSound f75 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p75
  · intro a ha; simp [p75] at ha; subst a; trivial
  · exact checked75
theorem derived75 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c75 := by
  apply localUnsat_implies_entails f75 [c74, c13] c75 unsat75 (by rfl) a
  have h0 : Entails.eval a c74 := derived74 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c76 : DefaultClause 29 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f76 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c74, some c73, some c70, some c39, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p76 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked76 : lratChecker f76 p76 = .success := by decide +kernel
theorem unsat76 : Unsatisfiable (PosFin 29) f76 := by
  apply lratCheckerSound f76 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p76
  · intro a ha; simp [p76] at ha; subst a; trivial
  · exact checked76
theorem derived76 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c76 := by
  apply localUnsat_implies_entails f76 [c74, c73, c70, c39] c76 unsat76 (by rfl) a
  have h0 : Entails.eval a c74 := derived74 a h
  have h1 : Entails.eval a c73 := derived73 a h
  have h2 : Entails.eval a c70 := derived70 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c77 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f77 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c75, some c70, some c61, some c4, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p77 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked77 : lratChecker f77 p77 = .success := by decide +kernel
theorem unsat77 : Unsatisfiable (PosFin 29) f77 := by
  apply lratCheckerSound f77 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p77
  · intro a ha; simp [p77] at ha; subst a; trivial
  · exact checked77
theorem derived77 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c77 := by
  apply localUnsat_implies_entails f77 [c75, c70, c61, c4] c77 unsat77 (by rfl) a
  have h0 : Entails.eval a c75 := derived75 a h
  have h1 : Entails.eval a c70 := derived70 a h
  have h2 : Entails.eval a c61 := derived61 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c78 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f78 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c76, some c77, some c73, some c71, some c38]
def p78 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked78 : lratChecker f78 p78 = .success := by decide +kernel
theorem unsat78 : Unsatisfiable (PosFin 29) f78 := by
  apply lratCheckerSound f78 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p78
  · intro a ha; simp [p78] at ha; subst a; trivial
  · exact checked78
theorem derived78 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c78 := by
  apply localUnsat_implies_entails f78 [c76, c77, c73, c71, c38] c78 unsat78 (by rfl) a
  have h0 : Entails.eval a c76 := derived76 a h
  have h1 : Entails.eval a c77 := derived77 a h
  have h2 : Entails.eval a c73 := derived73 a h
  have h3 : Entails.eval a c71 := derived71 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived78

end CochromaticTwenty.Certificates.Z12Direct_4_3_7
