import MerLeanExperiment.Certificates.Z8DirectTriangleCycle5.Inputs

/-! Generated from the actual pinned z8direct_triangle_cycle5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z8DirectTriangleCycle5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c84 : DefaultClause 16 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f84 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c6, some c11, some c27, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p84 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked84 : lratChecker f84 p84 = .success := by decide +kernel
theorem unsat84 : Unsatisfiable (PosFin 16) f84 := by
  apply lratCheckerSound f84 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p84
  · intro a ha; simp [p84] at ha; subst a; trivial
  · exact checked84
theorem derived84 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c84 := by
  apply localUnsat_implies_entails f84 [c6, c11, c27] c84 unsat84 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c85 : DefaultClause 16 := directClause [(⟨7, by decide⟩, false), (⟨14, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f85 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c1, some c15, some c9, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p85 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked85 : lratChecker f85 p85 = .success := by decide +kernel
theorem unsat85 : Unsatisfiable (PosFin 16) f85 := by
  apply lratCheckerSound f85 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p85
  · intro a ha; simp [p85] at ha; subst a; trivial
  · exact checked85
theorem derived85 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c85 := by
  apply localUnsat_implies_entails f85 [c1, c15, c9] c85 unsat85 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c86 : DefaultClause 16 := directClause [(⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f86 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c85, some c3, some c8, some c11, some c42, some c46, some c78, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p86 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked86 : lratChecker f86 p86 = .success := by decide +kernel
theorem unsat86 : Unsatisfiable (PosFin 16) f86 := by
  apply lratCheckerSound f86 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p86
  · intro a ha; simp [p86] at ha; subst a; trivial
  · exact checked86
theorem derived86 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c86 := by
  apply localUnsat_implies_entails f86 [c85, c3, c8, c11, c42, c46, c78] c86 unsat86 (by rfl) a
  have h0 : Entails.eval a c85 := derived85 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c87 : DefaultClause 16 := directClause [(⟨9, by decide⟩, true), (⟨14, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f87 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c86, some c85, some c17, some c29, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p87 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked87 : lratChecker f87 p87 = .success := by decide +kernel
theorem unsat87 : Unsatisfiable (PosFin 16) f87 := by
  apply lratCheckerSound f87 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p87
  · intro a ha; simp [p87] at ha; subst a; trivial
  · exact checked87
theorem derived87 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c87 := by
  apply localUnsat_implies_entails f87 [c86, c85, c17, c29] c87 unsat87 (by rfl) a
  have h0 : Entails.eval a c86 := derived86 a h
  have h1 : Entails.eval a c85 := derived85 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c88 : DefaultClause 16 := directClause [(⟨1, by decide⟩, false), (⟨14, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f88 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c87, some c47, some c61, some c73, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p88 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked88 : lratChecker f88 p88 = .success := by decide +kernel
theorem unsat88 : Unsatisfiable (PosFin 16) f88 := by
  apply lratCheckerSound f88 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p88
  · intro a ha; simp [p88] at ha; subst a; trivial
  · exact checked88
theorem derived88 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c88 := by
  apply localUnsat_implies_entails f88 [c87, c47, c61, c73] c88 unsat88 (by rfl) a
  have h0 : Entails.eval a c87 := derived87 a h
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c89 : DefaultClause 16 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f89 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c85, some c87, some c8, some c88, some c82, some c59, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p89 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked89 : lratChecker f89 p89 = .success := by decide +kernel
theorem unsat89 : Unsatisfiable (PosFin 16) f89 := by
  apply lratCheckerSound f89 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p89
  · intro a ha; simp [p89] at ha; subst a; trivial
  · exact checked89
theorem derived89 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c89 := by
  apply localUnsat_implies_entails f89 [c85, c87, c8, c88, c82, c59] c89 unsat89 (by rfl) a
  have h0 : Entails.eval a c85 := derived85 a h
  have h1 : Entails.eval a c87 := derived87 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c88 := derived88 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c90 : DefaultClause 16 := directClause [(⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f90 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c89, some c18, some c59, some c38, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p90 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked90 : lratChecker f90 p90 = .success := by decide +kernel
theorem unsat90 : Unsatisfiable (PosFin 16) f90 := by
  apply lratCheckerSound f90 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p90
  · intro a ha; simp [p90] at ha; subst a; trivial
  · exact checked90
theorem derived90 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c90 := by
  apply localUnsat_implies_entails f90 [c89, c18, c59, c38] c90 unsat90 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c91 : DefaultClause 16 := directClause [(⟨10, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f91 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c54, some c58, some c76, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p91 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked91 : lratChecker f91 p91 = .success := by decide +kernel
theorem unsat91 : Unsatisfiable (PosFin 16) f91 := by
  apply lratCheckerSound f91 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p91
  · intro a ha; simp [p91] at ha; subst a; trivial
  · exact checked91
theorem derived91 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c91 := by
  apply localUnsat_implies_entails f91 [c54, c58, c76] c91 unsat91 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c92 : DefaultClause 16 := directClause [(⟨11, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f92 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c12, some c28, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p92 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2]]
theorem checked92 : lratChecker f92 p92 = .success := by decide +kernel
theorem unsat92 : Unsatisfiable (PosFin 16) f92 := by
  apply lratCheckerSound f92 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p92
  · intro a ha; simp [p92] at ha; subst a; trivial
  · exact checked92
theorem derived92 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c92 := by
  apply localUnsat_implies_entails f92 [c12, c28] c92 unsat92 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c93 : DefaultClause 16 := directClause [(⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f93 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c89, some c91, some c90, some c92, some c34, some c68, some c38, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p93 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked93 : lratChecker f93 p93 = .success := by decide +kernel
theorem unsat93 : Unsatisfiable (PosFin 16) f93 := by
  apply lratCheckerSound f93 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p93
  · intro a ha; simp [p93] at ha; subst a; trivial
  · exact checked93
theorem derived93 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c93 := by
  apply localUnsat_implies_entails f93 [c89, c91, c90, c92, c34, c68, c38] c93 unsat93 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c91 := derived91 a h
  have h2 : Entails.eval a c90 := derived90 a h
  have h3 : Entails.eval a c92 := derived92 a h
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c94 : DefaultClause 16 := directClause [(⟨11, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f94 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c34, some c68, some c38, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p94 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked94 : lratChecker f94 p94 = .success := by decide +kernel
theorem unsat94 : Unsatisfiable (PosFin 16) f94 := by
  apply lratCheckerSound f94 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p94
  · intro a ha; simp [p94] at ha; subst a; trivial
  · exact checked94
theorem derived94 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c94 := by
  apply localUnsat_implies_entails f94 [c34, c68, c38] c94 unsat94 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c95 : DefaultClause 16 := directClause [(⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f95 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c89, some c94, some c33, some c92, some c71, some c83, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p95 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked95 : lratChecker f95 p95 = .success := by decide +kernel
theorem unsat95 : Unsatisfiable (PosFin 16) f95 := by
  apply lratCheckerSound f95 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p95
  · intro a ha; simp [p95] at ha; subst a; trivial
  · exact checked95
theorem derived95 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c95 := by
  apply localUnsat_implies_entails f95 [c89, c94, c33, c92, c71, c83] c95 unsat95 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c94 := derived94 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c92 := derived92 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c96 : DefaultClause 16 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f96 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c93, some c89, some c83, some c50, some c44, some c71, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p96 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked96 : lratChecker f96 p96 = .success := by decide +kernel
theorem unsat96 : Unsatisfiable (PosFin 16) f96 := by
  apply lratCheckerSound f96 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p96
  · intro a ha; simp [p96] at ha; subst a; trivial
  · exact checked96
theorem derived96 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c96 := by
  apply localUnsat_implies_entails f96 [c93, c89, c83, c50, c44, c71] c96 unsat96 (by rfl) a
  have h0 : Entails.eval a c93 := derived93 a h
  have h1 : Entails.eval a c89 := derived89 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c97 : DefaultClause 16 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f97 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c89, some c93, some c95, some c96, some c43, some c18, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p97 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked97 : lratChecker f97 p97 = .success := by decide +kernel
theorem unsat97 : Unsatisfiable (PosFin 16) f97 := by
  apply lratCheckerSound f97 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p97
  · intro a ha; simp [p97] at ha; subst a; trivial
  · exact checked97
theorem derived97 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c97 := by
  apply localUnsat_implies_entails f97 [c89, c93, c95, c96, c43, c18] c97 unsat97 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c93 := derived93 a h
  have h2 : Entails.eval a c95 := derived95 a h
  have h3 : Entails.eval a c96 := derived96 a h
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c98 : DefaultClause 16 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f98 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c18, some c92, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p98 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2]]
theorem checked98 : lratChecker f98 p98 = .success := by decide +kernel
theorem unsat98 : Unsatisfiable (PosFin 16) f98 := by
  apply lratCheckerSound f98 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p98
  · intro a ha; simp [p98] at ha; subst a; trivial
  · exact checked98
theorem derived98 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c98 := by
  apply localUnsat_implies_entails f98 [c18, c92] c98 unsat98 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c92 := derived92 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c99 : DefaultClause 16 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f99 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c97, some c89, some c98, some c17, some c23, some c5, some c25, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p99 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked99 : lratChecker f99 p99 = .success := by decide +kernel
theorem unsat99 : Unsatisfiable (PosFin 16) f99 := by
  apply lratCheckerSound f99 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p99
  · intro a ha; simp [p99] at ha; subst a; trivial
  · exact checked99
theorem derived99 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c99 := by
  apply localUnsat_implies_entails f99 [c97, c89, c98, c17, c23, c5, c25] c99 unsat99 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c89 := derived89 a h
  have h2 : Entails.eval a c98 := derived98 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c100 : DefaultClause 16 := directClause [(⟨11, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f100 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c99, some c83, some c97, some c17, some c14, some c23, some c34, some c74, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p100 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked100 : lratChecker f100 p100 = .success := by decide +kernel
theorem unsat100 : Unsatisfiable (PosFin 16) f100 := by
  apply lratCheckerSound f100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p100
  · intro a ha; simp [p100] at ha; subst a; trivial
  · exact checked100
theorem derived100 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c100 := by
  apply localUnsat_implies_entails f100 [c99, c83, c97, c17, c14, c23, c34, c74] c100 unsat100 (by rfl) a
  have h0 : Entails.eval a c99 := derived99 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c97 := derived97 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c101 : DefaultClause 16 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f101 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c89, some c99, some c83, some c100, some c77, some c71, some c63, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p101 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked101 : lratChecker f101 p101 = .success := by decide +kernel
theorem unsat101 : Unsatisfiable (PosFin 16) f101 := by
  apply lratCheckerSound f101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p101
  · intro a ha; simp [p101] at ha; subst a; trivial
  · exact checked101
theorem derived101 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c101 := by
  apply localUnsat_implies_entails f101 [c89, c99, c83, c100, c77, c71, c63] c101 unsat101 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c99 := derived99 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c100 := derived100 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c102 : DefaultClause 16 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f102 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c101, some c36, some c33, some c35, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p102 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked102 : lratChecker f102 p102 = .success := by decide +kernel
theorem unsat102 : Unsatisfiable (PosFin 16) f102 := by
  apply lratCheckerSound f102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p102
  · intro a ha; simp [p102] at ha; subst a; trivial
  · exact checked102
theorem derived102 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c102 := by
  apply localUnsat_implies_entails f102 [c101, c36, c33, c35] c102 unsat102 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c103 : DefaultClause 16 := directClause [(⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨2, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f103 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c42, some c70, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p103 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2]]
theorem checked103 : lratChecker f103 p103 = .success := by decide +kernel
theorem unsat103 : Unsatisfiable (PosFin 16) f103 := by
  apply lratCheckerSound f103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p103
  · intro a ha; simp [p103] at ha; subst a; trivial
  · exact checked103
theorem derived103 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c103 := by
  apply localUnsat_implies_entails f103 [c42, c70] c103 unsat103 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c104 : DefaultClause 16 := directClause [(⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f104 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c101, some c21, some c10, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p104 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked104 : lratChecker f104 p104 = .success := by decide +kernel
theorem unsat104 : Unsatisfiable (PosFin 16) f104 := by
  apply lratCheckerSound f104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p104
  · intro a ha; simp [p104] at ha; subst a; trivial
  · exact checked104
theorem derived104 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c104 := by
  apply localUnsat_implies_entails f104 [c101, c21, c10] c104 unsat104 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c105 : DefaultClause 16 := directClause [(⟨14, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f105 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c41, some c71, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p105 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2]]
theorem checked105 : lratChecker f105 p105 = .success := by decide +kernel
theorem unsat105 : Unsatisfiable (PosFin 16) f105 := by
  apply lratCheckerSound f105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p105
  · intro a ha; simp [p105] at ha; subst a; trivial
  · exact checked105
theorem derived105 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c105 := by
  apply localUnsat_implies_entails f105 [c41, c71] c105 unsat105 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c106 : DefaultClause 16 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f106 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c101, some c102, some c105, some c103, some c13, some c21, some c10, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p106 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked106 : lratChecker f106 p106 = .success := by decide +kernel
theorem unsat106 : Unsatisfiable (PosFin 16) f106 := by
  apply lratCheckerSound f106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p106
  · intro a ha; simp [p106] at ha; subst a; trivial
  · exact checked106
theorem derived106 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c106 := by
  apply localUnsat_implies_entails f106 [c101, c102, c105, c103, c13, c21, c10] c106 unsat106 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c102 := derived102 a h
  have h2 : Entails.eval a c105 := derived105 a h
  have h3 : Entails.eval a c103 := derived103 a h
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c107 : DefaultClause 16 := directClause [(⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f107 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c101, some c106, some c2, some c13, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p107 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked107 : lratChecker f107 p107 = .success := by decide +kernel
theorem unsat107 : Unsatisfiable (PosFin 16) f107 := by
  apply lratCheckerSound f107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p107
  · intro a ha; simp [p107] at ha; subst a; trivial
  · exact checked107
theorem derived107 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c107 := by
  apply localUnsat_implies_entails f107 [c101, c106, c2, c13] c107 unsat107 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c106 := derived106 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c108 : DefaultClause 16 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f108 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c107, some c105, some c103, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p108 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked108 : lratChecker f108 p108 = .success := by decide +kernel
theorem unsat108 : Unsatisfiable (PosFin 16) f108 := by
  apply lratCheckerSound f108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p108
  · intro a ha; simp [p108] at ha; subst a; trivial
  · exact checked108
theorem derived108 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c108 := by
  apply localUnsat_implies_entails f108 [c107, c105, c103] c108 unsat108 (by rfl) a
  have h0 : Entails.eval a c107 := derived107 a h
  have h1 : Entails.eval a c105 := derived105 a h
  have h2 : Entails.eval a c103 := derived103 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c109 : DefaultClause 16 := directClause [(⟨12, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f109 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c101, some c51, some c56, some c75, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p109 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked109 : lratChecker f109 p109 = .success := by decide +kernel
theorem unsat109 : Unsatisfiable (PosFin 16) f109 := by
  apply lratCheckerSound f109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p109
  · intro a ha; simp [p109] at ha; subst a; trivial
  · exact checked109
theorem derived109 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c109 := by
  apply localUnsat_implies_entails f109 [c101, c51, c56, c75] c109 unsat109 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c110 : DefaultClause 16 := directClause [(⟨14, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f110 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c108, some c107, some c84, some c49, some c109, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p110 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked110 : lratChecker f110 p110 = .success := by decide +kernel
theorem unsat110 : Unsatisfiable (PosFin 16) f110 := by
  apply lratCheckerSound f110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p110
  · intro a ha; simp [p110] at ha; subst a; trivial
  · exact checked110
theorem derived110 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c110 := by
  apply localUnsat_implies_entails f110 [c108, c107, c84, c49, c109] c110 unsat110 (by rfl) a
  have h0 : Entails.eval a c108 := derived108 a h
  have h1 : Entails.eval a c107 := derived107 a h
  have h2 : Entails.eval a c84 := derived84 a h
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c109 := derived109 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c111 : DefaultClause 16 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f111 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c108, some c110, some c41, some c62, some c77, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p111 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked111 : lratChecker f111 p111 = .success := by decide +kernel
theorem unsat111 : Unsatisfiable (PosFin 16) f111 := by
  apply lratCheckerSound f111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p111
  · intro a ha; simp [p111] at ha; subst a; trivial
  · exact checked111
theorem derived111 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c111 := by
  apply localUnsat_implies_entails f111 [c108, c110, c41, c62, c77] c111 unsat111 (by rfl) a
  have h0 : Entails.eval a c108 := derived108 a h
  have h1 : Entails.eval a c110 := derived110 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c112 : DefaultClause 16 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f112 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c66, some c65, some c64, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p112 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked112 : lratChecker f112 p112 = .success := by decide +kernel
theorem unsat112 : Unsatisfiable (PosFin 16) f112 := by
  apply lratCheckerSound f112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p112
  · intro a ha; simp [p112] at ha; subst a; trivial
  · exact checked112
theorem derived112 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c112 := by
  apply localUnsat_implies_entails f112 [c66, c65, c64] c112 unsat112 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c113 : DefaultClause 16 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f113 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c101, some c27, some c16, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p113 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked113 : lratChecker f113 p113 = .success := by decide +kernel
theorem unsat113 : Unsatisfiable (PosFin 16) f113 := by
  apply lratCheckerSound f113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p113
  · intro a ha; simp [p113] at ha; subst a; trivial
  · exact checked113
theorem derived113 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c113 := by
  apply localUnsat_implies_entails f113 [c101, c27, c16] c113 unsat113 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c114 : DefaultClause 16 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f114 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c101, some c10, some c113, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p114 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked114 : lratChecker f114 p114 = .success := by decide +kernel
theorem unsat114 : Unsatisfiable (PosFin 16) f114 := by
  apply lratCheckerSound f114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p114
  · intro a ha; simp [p114] at ha; subst a; trivial
  · exact checked114
theorem derived114 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c114 := by
  apply localUnsat_implies_entails f114 [c101, c10, c113] c114 unsat114 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c113 := derived113 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c115 : DefaultClause 16 := directClause [(⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f115 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c111, some c80, some c45, some c109, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p115 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked115 : lratChecker f115 p115 = .success := by decide +kernel
theorem unsat115 : Unsatisfiable (PosFin 16) f115 := by
  apply lratCheckerSound f115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p115
  · intro a ha; simp [p115] at ha; subst a; trivial
  · exact checked115
theorem derived115 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c115 := by
  apply localUnsat_implies_entails f115 [c111, c80, c45, c109] c115 unsat115 (by rfl) a
  have h0 : Entails.eval a c111 := derived111 a h
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c109 := derived109 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c116 : DefaultClause 16 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f116 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c112, some c115, some c114, some c50, some c54, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p116 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked116 : lratChecker f116 p116 = .success := by decide +kernel
theorem unsat116 : Unsatisfiable (PosFin 16) f116 := by
  apply lratCheckerSound f116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p116
  · intro a ha; simp [p116] at ha; subst a; trivial
  · exact checked116
theorem derived116 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c116 := by
  apply localUnsat_implies_entails f116 [c112, c115, c114, c50, c54] c116 unsat116 (by rfl) a
  have h0 : Entails.eval a c112 := derived112 a h
  have h1 : Entails.eval a c115 := derived115 a h
  have h2 : Entails.eval a c114 := derived114 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c117 : DefaultClause 16 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f117 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c44, some c19, some c109, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p117 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked117 : lratChecker f117 p117 = .success := by decide +kernel
theorem unsat117 : Unsatisfiable (PosFin 16) f117 := by
  apply lratCheckerSound f117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p117
  · intro a ha; simp [p117] at ha; subst a; trivial
  · exact checked117
theorem derived117 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c117 := by
  apply localUnsat_implies_entails f117 [c44, c19, c109] c117 unsat117 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c109 := derived109 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c118 : DefaultClause 16 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f118 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c111, some c116, some c117, some c114, some c80, some c69, some c72, some c109, some c79, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p118 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked118 : lratChecker f118 p118 = .success := by decide +kernel
theorem unsat118 : Unsatisfiable (PosFin 16) f118 := by
  apply lratCheckerSound f118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p118
  · intro a ha; simp [p118] at ha; subst a; trivial
  · exact checked118
theorem derived118 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c118 := by
  apply localUnsat_implies_entails f118 [c111, c116, c117, c114, c80, c69, c72, c109, c79] c118 unsat118 (by rfl) a
  have h0 : Entails.eval a c111 := derived111 a h
  have h1 : Entails.eval a c116 := derived116 a h
  have h2 : Entails.eval a c117 := derived117 a h
  have h3 : Entails.eval a c114 := derived114 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c109 := derived109 a h
  have h8 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c119 : DefaultClause 16 := directClause [(⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f119 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c118, some c109, some c25, some c20, some c37, some c53, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p119 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked119 : lratChecker f119 p119 = .success := by decide +kernel
theorem unsat119 : Unsatisfiable (PosFin 16) f119 := by
  apply lratCheckerSound f119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p119
  · intro a ha; simp [p119] at ha; subst a; trivial
  · exact checked119
theorem derived119 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c119 := by
  apply localUnsat_implies_entails f119 [c118, c109, c25, c20, c37, c53] c119 unsat119 (by rfl) a
  have h0 : Entails.eval a c118 := derived118 a h
  have h1 : Entails.eval a c109 := derived109 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c120 : DefaultClause 16 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f120 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c118, some c109, some c53, some c52, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p120 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked120 : lratChecker f120 p120 = .success := by decide +kernel
theorem unsat120 : Unsatisfiable (PosFin 16) f120 := by
  apply lratCheckerSound f120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p120
  · intro a ha; simp [p120] at ha; subst a; trivial
  · exact checked120
theorem derived120 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c120 := by
  apply localUnsat_implies_entails f120 [c118, c109, c53, c52] c120 unsat120 (by rfl) a
  have h0 : Entails.eval a c118 := derived118 a h
  have h1 : Entails.eval a c109 := derived109 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c121 : DefaultClause 16 := directClause [(⟨7, by decide⟩, false), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f121 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c114, some c104, some c26, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p121 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked121 : lratChecker f121 p121 = .success := by decide +kernel
theorem unsat121 : Unsatisfiable (PosFin 16) f121 := by
  apply lratCheckerSound f121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p121
  · intro a ha; simp [p121] at ha; subst a; trivial
  · exact checked121
theorem derived121 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c121 := by
  apply localUnsat_implies_entails f121 [c114, c104, c26] c121 unsat121 (by rfl) a
  have h0 : Entails.eval a c114 := derived114 a h
  have h1 : Entails.eval a c104 := derived104 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c122 : DefaultClause 16 := directClause [(⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f122 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c118, some c114, some c119, some c98, some c120, some c121, some c24, some c46, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p122 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked122 : lratChecker f122 p122 = .success := by decide +kernel
theorem unsat122 : Unsatisfiable (PosFin 16) f122 := by
  apply lratCheckerSound f122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p122
  · intro a ha; simp [p122] at ha; subst a; trivial
  · exact checked122
theorem derived122 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c122 := by
  apply localUnsat_implies_entails f122 [c118, c114, c119, c98, c120, c121, c24, c46] c122 unsat122 (by rfl) a
  have h0 : Entails.eval a c118 := derived118 a h
  have h1 : Entails.eval a c114 := derived114 a h
  have h2 : Entails.eval a c119 := derived119 a h
  have h3 : Entails.eval a c98 := derived98 a h
  have h4 : Entails.eval a c120 := derived120 a h
  have h5 : Entails.eval a c121 := derived121 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c123 : DefaultClause 16 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f123 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c101, some c31, some c32, some c30, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p123 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked123 : lratChecker f123 p123 = .success := by decide +kernel
theorem unsat123 : Unsatisfiable (PosFin 16) f123 := by
  apply lratCheckerSound f123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p123
  · intro a ha; simp [p123] at ha; subst a; trivial
  · exact checked123
theorem derived123 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c123 := by
  apply localUnsat_implies_entails f123 [c101, c31, c32, c30] c123 unsat123 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c124 : DefaultClause 16 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f124 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c114, some c122, some c123, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p124 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked124 : lratChecker f124 p124 = .success := by decide +kernel
theorem unsat124 : Unsatisfiable (PosFin 16) f124 := by
  apply lratCheckerSound f124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p124
  · intro a ha; simp [p124] at ha; subst a; trivial
  · exact checked124
theorem derived124 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c124 := by
  apply localUnsat_implies_entails f124 [c114, c122, c123] c124 unsat124 (by rfl) a
  have h0 : Entails.eval a c114 := derived114 a h
  have h1 : Entails.eval a c122 := derived122 a h
  have h2 : Entails.eval a c123 := derived123 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c125 : DefaultClause 16 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f125 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c118, some c124, some c101, some c123, some c109, some c119, some c98, some c82, some c55, some c57, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p125 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked125 : lratChecker f125 p125 = .success := by decide +kernel
theorem unsat125 : Unsatisfiable (PosFin 16) f125 := by
  apply lratCheckerSound f125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p125
  · intro a ha; simp [p125] at ha; subst a; trivial
  · exact checked125
theorem derived125 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c125 := by
  apply localUnsat_implies_entails f125 [c118, c124, c101, c123, c109, c119, c98, c82, c55, c57] c125 unsat125 (by rfl) a
  have h0 : Entails.eval a c118 := derived118 a h
  have h1 : Entails.eval a c124 := derived124 a h
  have h2 : Entails.eval a c101 := derived101 a h
  have h3 : Entails.eval a c123 := derived123 a h
  have h4 : Entails.eval a c109 := derived109 a h
  have h5 : Entails.eval a c119 := derived119 a h
  have h6 : Entails.eval a c98 := derived98 a h
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c126 : DefaultClause 16 := directClause [(⟨12, by decide⟩, false), (⟨1, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f126 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c124, some c57, some c39, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p126 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked126 : lratChecker f126 p126 = .success := by decide +kernel
theorem unsat126 : Unsatisfiable (PosFin 16) f126 := by
  apply lratCheckerSound f126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p126
  · intro a ha; simp [p126] at ha; subst a; trivial
  · exact checked126
theorem derived126 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c126 := by
  apply localUnsat_implies_entails f126 [c124, c57, c39] c126 unsat126 (by rfl) a
  have h0 : Entails.eval a c124 := derived124 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c127 : DefaultClause 16 := directClause [(⟨1, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f127 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c109, some c126, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p127 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2]]
theorem checked127 : lratChecker f127 p127 = .success := by decide +kernel
theorem unsat127 : Unsatisfiable (PosFin 16) f127 := by
  apply lratCheckerSound f127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p127
  · intro a ha; simp [p127] at ha; subst a; trivial
  · exact checked127
theorem derived127 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c127 := by
  apply localUnsat_implies_entails f127 [c109, c126] c127 unsat127 (by rfl) a
  have h0 : Entails.eval a c109 := derived109 a h
  have h1 : Entails.eval a c126 := derived126 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c128 : DefaultClause 16 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f128 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c118, some c127, some c43, some c3, some c98, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p128 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked128 : lratChecker f128 p128 = .success := by decide +kernel
theorem unsat128 : Unsatisfiable (PosFin 16) f128 := by
  apply lratCheckerSound f128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p128
  · intro a ha; simp [p128] at ha; subst a; trivial
  · exact checked128
theorem derived128 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c128 := by
  apply localUnsat_implies_entails f128 [c118, c127, c43, c3, c98] c128 unsat128 (by rfl) a
  have h0 : Entails.eval a c118 := derived118 a h
  have h1 : Entails.eval a c127 := derived127 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c98 := derived98 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c129 : DefaultClause 16 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f129 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c125, some c128, some c127, some c60, some c81, some c7, some c74, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p129 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked129 : lratChecker f129 p129 = .success := by decide +kernel
theorem unsat129 : Unsatisfiable (PosFin 16) f129 := by
  apply lratCheckerSound f129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p129
  · intro a ha; simp [p129] at ha; subst a; trivial
  · exact checked129
theorem derived129 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c129 := by
  apply localUnsat_implies_entails f129 [c125, c128, c127, c60, c81, c7, c74] c129 unsat129 (by rfl) a
  have h0 : Entails.eval a c125 := derived125 a h
  have h1 : Entails.eval a c128 := derived128 a h
  have h2 : Entails.eval a c127 := derived127 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c130 : DefaultClause 16 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f130 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c125, some c101, some c124, some c22, some c4, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p130 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked130 : lratChecker f130 p130 = .success := by decide +kernel
theorem unsat130 : Unsatisfiable (PosFin 16) f130 := by
  apply lratCheckerSound f130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p130
  · intro a ha; simp [p130] at ha; subst a; trivial
  · exact checked130
theorem derived130 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c130 := by
  apply localUnsat_implies_entails f130 [c125, c101, c124, c22, c4] c130 unsat130 (by rfl) a
  have h0 : Entails.eval a c125 := derived125 a h
  have h1 : Entails.eval a c101 := derived101 a h
  have h2 : Entails.eval a c124 := derived124 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c131 : DefaultClause 16 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f131 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c130, some c129, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p131 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2]]
theorem checked131 : lratChecker f131 p131 = .success := by decide +kernel
theorem unsat131 : Unsatisfiable (PosFin 16) f131 := by
  apply lratCheckerSound f131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p131
  · intro a ha; simp [p131] at ha; subst a; trivial
  · exact checked131
theorem derived131 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c131 := by
  apply localUnsat_implies_entails f131 [c130, c129] c131 unsat131 (by rfl) a
  have h0 : Entails.eval a c130 := derived130 a h
  have h1 : Entails.eval a c129 := derived129 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c132 : DefaultClause 16 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f132 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c131, some c124, some c101, some c40, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p132 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked132 : lratChecker f132 p132 = .success := by decide +kernel
theorem unsat132 : Unsatisfiable (PosFin 16) f132 := by
  apply lratCheckerSound f132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p132
  · intro a ha; simp [p132] at ha; subst a; trivial
  · exact checked132
theorem derived132 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c132 := by
  apply localUnsat_implies_entails f132 [c131, c124, c101, c40] c132 unsat132 (by rfl) a
  have h0 : Entails.eval a c131 := derived131 a h
  have h1 : Entails.eval a c124 := derived124 a h
  have h2 : Entails.eval a c101 := derived101 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c133 : DefaultClause 16 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f133 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c132, some c131, some c101, some c55, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p133 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked133 : lratChecker f133 p133 = .success := by decide +kernel
theorem unsat133 : Unsatisfiable (PosFin 16) f133 := by
  apply lratCheckerSound f133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p133
  · intro a ha; simp [p133] at ha; subst a; trivial
  · exact checked133
theorem derived133 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c133 := by
  apply localUnsat_implies_entails f133 [c132, c131, c101, c55] c133 unsat133 (by rfl) a
  have h0 : Entails.eval a c132 := derived132 a h
  have h1 : Entails.eval a c131 := derived131 a h
  have h2 : Entails.eval a c101 := derived101 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c134 : DefaultClause 16 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f134 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c132, some c131, some c101, some c67, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p134 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked134 : lratChecker f134 p134 = .success := by decide +kernel
theorem unsat134 : Unsatisfiable (PosFin 16) f134 := by
  apply lratCheckerSound f134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p134
  · intro a ha; simp [p134] at ha; subst a; trivial
  · exact checked134
theorem derived134 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c134 := by
  apply localUnsat_implies_entails f134 [c132, c131, c101, c67] c134 unsat134 (by rfl) a
  have h0 : Entails.eval a c132 := derived132 a h
  have h1 : Entails.eval a c131 := derived131 a h
  have h2 : Entails.eval a c101 := derived101 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c135 : DefaultClause 16 := directClause [] (by decide +kernel) (by decide +kernel)
def f135 : DefaultFormula 16 := DefaultFormula.ofArray #[none, some c134, some c133, some c131, some c101, some c48]
def p135 : List (Action (DefaultClause 16) (PosFin 16)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked135 : lratChecker f135 p135 = .success := by decide +kernel
theorem unsat135 : Unsatisfiable (PosFin 16) f135 := by
  apply lratCheckerSound f135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p135
  · intro a ha; simp [p135] at ha; subst a; trivial
  · exact checked135
theorem derived135 (a : PosFin 16 → Bool) (h : InputSat a) : Entails.eval a c135 := by
  apply localUnsat_implies_entails f135 [c134, c133, c131, c101, c48] c135 unsat135 (by rfl) a
  have h0 : Entails.eval a c134 := derived134 a h
  have h1 : Entails.eval a c133 := derived133 a h
  have h2 : Entails.eval a c131 := derived131 a h
  have h3 : Entails.eval a c101 := derived101 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived135

end CochromaticTwenty.Certificates.Z8DirectTriangleCycle5
