import MerLeanExperiment.Certificates.Z12Direct_5_5_3.Inputs

/-! Generated from the actual pinned z12direct_5_5_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c111 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f111 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c18, some c19, some c20, some c59, some c32, some c35, some c81, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p111 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked111 : lratChecker f111 p111 = .success := by decide +kernel
theorem unsat111 : Unsatisfiable (PosFin 31) f111 := by
  apply lratCheckerSound f111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p111
  · intro a ha; simp [p111] at ha; subst a; trivial
  · exact checked111
theorem derived111 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c111 := by
  apply localUnsat_implies_entails f111 [c18, c19, c20, c59, c32, c35, c81] c111 unsat111 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c112 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f112 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c111, some c7, some c60, some c79, some c64, some c28, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p112 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked112 : lratChecker f112 p112 = .success := by decide +kernel
theorem unsat112 : Unsatisfiable (PosFin 31) f112 := by
  apply lratCheckerSound f112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p112
  · intro a ha; simp [p112] at ha; subst a; trivial
  · exact checked112
theorem derived112 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c112 := by
  apply localUnsat_implies_entails f112 [c111, c7, c60, c79, c64, c28] c112 unsat112 (by rfl) a
  have h0 : Entails.eval a c111 := derived111 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c113 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f113 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c111, some c112, some c2, some c15, some c22, some c79, some c30, some c62, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p113 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked113 : lratChecker f113 p113 = .success := by decide +kernel
theorem unsat113 : Unsatisfiable (PosFin 31) f113 := by
  apply lratCheckerSound f113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p113
  · intro a ha; simp [p113] at ha; subst a; trivial
  · exact checked113
theorem derived113 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c113 := by
  apply localUnsat_implies_entails f113 [c111, c112, c2, c15, c22, c79, c30, c62] c113 unsat113 (by rfl) a
  have h0 : Entails.eval a c111 := derived111 a h
  have h1 : Entails.eval a c112 := derived112 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c114 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f114 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c108, some c20, some c78, some c31, some c69, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p114 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked114 : lratChecker f114 p114 = .success := by decide +kernel
theorem unsat114 : Unsatisfiable (PosFin 31) f114 := by
  apply lratCheckerSound f114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p114
  · intro a ha; simp [p114] at ha; subst a; trivial
  · exact checked114
theorem derived114 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c114 := by
  apply localUnsat_implies_entails f114 [c113, c108, c20, c78, c31, c69] c114 unsat114 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c115 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f115 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c15, some c114, some c40, some c82, some c1, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p115 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked115 : lratChecker f115 p115 = .success := by decide +kernel
theorem unsat115 : Unsatisfiable (PosFin 31) f115 := by
  apply lratCheckerSound f115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p115
  · intro a ha; simp [p115] at ha; subst a; trivial
  · exact checked115
theorem derived115 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c115 := by
  apply localUnsat_implies_entails f115 [c15, c114, c40, c82, c1] c115 unsat115 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c114 := derived114 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c116 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f116 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c108, some c115, some c2, some c23, some c44, some c7, some c103, some c109, some c106, some c90, some c67, some c28, some c64, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p116 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked116 : lratChecker f116 p116 = .success := by decide +kernel
theorem unsat116 : Unsatisfiable (PosFin 31) f116 := by
  apply lratCheckerSound f116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p116
  · intro a ha; simp [p116] at ha; subst a; trivial
  · exact checked116
theorem derived116 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c116 := by
  apply localUnsat_implies_entails f116 [c113, c108, c115, c2, c23, c44, c7, c103, c109, c106, c90, c67, c28, c64] c116 unsat116 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c115 := derived115 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c117 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f117 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c116, some c113, some c108, some c20, some c59, some c35, some c92, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p117 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked117 : lratChecker f117 p117 = .success := by decide +kernel
theorem unsat117 : Unsatisfiable (PosFin 31) f117 := by
  apply lratCheckerSound f117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p117
  · intro a ha; simp [p117] at ha; subst a; trivial
  · exact checked117
theorem derived117 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c117 := by
  apply localUnsat_implies_entails f117 [c116, c113, c108, c20, c59, c35, c92] c117 unsat117 (by rfl) a
  have h0 : Entails.eval a c116 := derived116 a h
  have h1 : Entails.eval a c113 := derived113 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c118 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f118 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c116, some c113, some c108, some c117, some c55, some c29, some c35, some c39, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p118 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked118 : lratChecker f118 p118 = .success := by decide +kernel
theorem unsat118 : Unsatisfiable (PosFin 31) f118 := by
  apply lratCheckerSound f118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p118
  · intro a ha; simp [p118] at ha; subst a; trivial
  · exact checked118
theorem derived118 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c118 := by
  apply localUnsat_implies_entails f118 [c116, c113, c108, c117, c55, c29, c35, c39] c118 unsat118 (by rfl) a
  have h0 : Entails.eval a c116 := derived116 a h
  have h1 : Entails.eval a c113 := derived113 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c117 := derived117 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c119 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f119 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c19, some c118, some c15, some c32, some c1, some c63, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p119 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked119 : lratChecker f119 p119 = .success := by decide +kernel
theorem unsat119 : Unsatisfiable (PosFin 31) f119 := by
  apply lratCheckerSound f119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p119
  · intro a ha; simp [p119] at ha; subst a; trivial
  · exact checked119
theorem derived119 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c119 := by
  apply localUnsat_implies_entails f119 [c19, c118, c15, c32, c1, c63] c119 unsat119 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c118 := derived118 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c120 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f120 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c116, some c119, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p120 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked120 : lratChecker f120 p120 = .success := by decide +kernel
theorem unsat120 : Unsatisfiable (PosFin 31) f120 := by
  apply lratCheckerSound f120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p120
  · intro a ha; simp [p120] at ha; subst a; trivial
  · exact checked120
theorem derived120 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c120 := by
  apply localUnsat_implies_entails f120 [c116, c119] c120 unsat120 (by rfl) a
  have h0 : Entails.eval a c116 := derived116 a h
  have h1 : Entails.eval a c119 := derived119 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c121 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f121 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c120, some c105, some c39, some c57, some c94, some c1, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p121 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked121 : lratChecker f121 p121 = .success := by decide +kernel
theorem unsat121 : Unsatisfiable (PosFin 31) f121 := by
  apply lratCheckerSound f121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p121
  · intro a ha; simp [p121] at ha; subst a; trivial
  · exact checked121
theorem derived121 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c121 := by
  apply localUnsat_implies_entails f121 [c120, c105, c39, c57, c94, c1] c121 unsat121 (by rfl) a
  have h0 : Entails.eval a c120 := derived120 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c122 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f122 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c120, some c105, some c121, some c33, some c48, some c32, some c57, some c30, some c9, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p122 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked122 : lratChecker f122 p122 = .success := by decide +kernel
theorem unsat122 : Unsatisfiable (PosFin 31) f122 := by
  apply lratCheckerSound f122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p122
  · intro a ha; simp [p122] at ha; subst a; trivial
  · exact checked122
theorem derived122 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c122 := by
  apply localUnsat_implies_entails f122 [c120, c105, c121, c33, c48, c32, c57, c30, c9] c122 unsat122 (by rfl) a
  have h0 : Entails.eval a c120 := derived120 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c121 := derived121 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c123 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f123 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c122, some c120, some c105, some c33, some c48, some c53, some c93, some c65, some c60, some c80, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p123 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked123 : lratChecker f123 p123 = .success := by decide +kernel
theorem unsat123 : Unsatisfiable (PosFin 31) f123 := by
  apply lratCheckerSound f123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p123
  · intro a ha; simp [p123] at ha; subst a; trivial
  · exact checked123
theorem derived123 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c123 := by
  apply localUnsat_implies_entails f123 [c122, c120, c105, c33, c48, c53, c93, c65, c60, c80] c123 unsat123 (by rfl) a
  have h0 : Entails.eval a c122 := derived122 a h
  have h1 : Entails.eval a c120 := derived120 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c124 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f124 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c123, some c39, some c122, some c120, some c22, some c1, some c108, some c80, some c102, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p124 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked124 : lratChecker f124 p124 = .success := by decide +kernel
theorem unsat124 : Unsatisfiable (PosFin 31) f124 := by
  apply lratCheckerSound f124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p124
  · intro a ha; simp [p124] at ha; subst a; trivial
  · exact checked124
theorem derived124 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c124 := by
  apply localUnsat_implies_entails f124 [c123, c39, c122, c120, c22, c1, c108, c80, c102] c124 unsat124 (by rfl) a
  have h0 : Entails.eval a c123 := derived123 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c122 := derived122 a h
  have h3 : Entails.eval a c120 := derived120 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c125 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f125 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c46, some c27, some c108, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p125 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked125 : lratChecker f125 p125 = .success := by decide +kernel
theorem unsat125 : Unsatisfiable (PosFin 31) f125 := by
  apply lratCheckerSound f125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p125
  · intro a ha; simp [p125] at ha; subst a; trivial
  · exact checked125
theorem derived125 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c125 := by
  apply localUnsat_implies_entails f125 [c46, c27, c108] c125 unsat125 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c126 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f126 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c39, some c124, some c125, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p126 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked126 : lratChecker f126 p126 = .success := by decide +kernel
theorem unsat126 : Unsatisfiable (PosFin 31) f126 := by
  apply lratCheckerSound f126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p126
  · intro a ha; simp [p126] at ha; subst a; trivial
  · exact checked126
theorem derived126 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c126 := by
  apply localUnsat_implies_entails f126 [c39, c124, c125] c126 unsat126 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c124 := derived124 a h
  have h2 : Entails.eval a c125 := derived125 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c127 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f127 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c123, some c126, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p127 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked127 : lratChecker f127 p127 = .success := by decide +kernel
theorem unsat127 : Unsatisfiable (PosFin 31) f127 := by
  apply lratCheckerSound f127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p127
  · intro a ha; simp [p127] at ha; subst a; trivial
  · exact checked127
theorem derived127 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c127 := by
  apply localUnsat_implies_entails f127 [c123, c126] c127 unsat127 (by rfl) a
  have h0 : Entails.eval a c123 := derived123 a h
  have h1 : Entails.eval a c126 := derived126 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c128 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f128 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c127, some c120, some c105, some c57, some c2, some c25, some c88, some c79, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p128 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked128 : lratChecker f128 p128 = .success := by decide +kernel
theorem unsat128 : Unsatisfiable (PosFin 31) f128 := by
  apply lratCheckerSound f128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p128
  · intro a ha; simp [p128] at ha; subst a; trivial
  · exact checked128
theorem derived128 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c128 := by
  apply localUnsat_implies_entails f128 [c127, c120, c105, c57, c2, c25, c88, c79] c128 unsat128 (by rfl) a
  have h0 : Entails.eval a c127 := derived127 a h
  have h1 : Entails.eval a c120 := derived120 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c129 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f129 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c127, some c120, some c105, some c128, some c84, some c61, some c2, some c74, some c79, some c86, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p129 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked129 : lratChecker f129 p129 = .success := by decide +kernel
theorem unsat129 : Unsatisfiable (PosFin 31) f129 := by
  apply lratCheckerSound f129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p129
  · intro a ha; simp [p129] at ha; subst a; trivial
  · exact checked129
theorem derived129 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c129 := by
  apply localUnsat_implies_entails f129 [c127, c120, c105, c128, c84, c61, c2, c74, c79, c86] c129 unsat129 (by rfl) a
  have h0 : Entails.eval a c127 := derived127 a h
  have h1 : Entails.eval a c120 := derived120 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c128 := derived128 a h
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c130 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f130 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c127, some c120, some c129, some c22, some c1, some c108, some c25, some c61, some c76, some c32, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p130 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked130 : lratChecker f130 p130 = .success := by decide +kernel
theorem unsat130 : Unsatisfiable (PosFin 31) f130 := by
  apply lratCheckerSound f130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p130
  · intro a ha; simp [p130] at ha; subst a; trivial
  · exact checked130
theorem derived130 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c130 := by
  apply localUnsat_implies_entails f130 [c127, c120, c129, c22, c1, c108, c25, c61, c76, c32] c130 unsat130 (by rfl) a
  have h0 : Entails.eval a c127 := derived127 a h
  have h1 : Entails.eval a c120 := derived120 a h
  have h2 : Entails.eval a c129 := derived129 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c131 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f131 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c130, some c127, some c120, some c108, some c25, some c32, some c58, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p131 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked131 : lratChecker f131 p131 = .success := by decide +kernel
theorem unsat131 : Unsatisfiable (PosFin 31) f131 := by
  apply lratCheckerSound f131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p131
  · intro a ha; simp [p131] at ha; subst a; trivial
  · exact checked131
theorem derived131 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c131 := by
  apply localUnsat_implies_entails f131 [c130, c127, c120, c108, c25, c32, c58] c131 unsat131 (by rfl) a
  have h0 : Entails.eval a c130 := derived130 a h
  have h1 : Entails.eval a c127 := derived127 a h
  have h2 : Entails.eval a c120 := derived120 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c132 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f132 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c131, some c130, some c32, some c41, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p132 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked132 : lratChecker f132 p132 = .success := by decide +kernel
theorem unsat132 : Unsatisfiable (PosFin 31) f132 := by
  apply lratCheckerSound f132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p132
  · intro a ha; simp [p132] at ha; subst a; trivial
  · exact checked132
theorem derived132 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c132 := by
  apply localUnsat_implies_entails f132 [c131, c130, c32, c41] c132 unsat132 (by rfl) a
  have h0 : Entails.eval a c131 := derived131 a h
  have h1 : Entails.eval a c130 := derived130 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c133 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f133 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c130, some c127, some c120, some c105, some c131, some c60, some c132, some c2, some c93, some c83, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p133 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked133 : lratChecker f133 p133 = .success := by decide +kernel
theorem unsat133 : Unsatisfiable (PosFin 31) f133 := by
  apply lratCheckerSound f133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p133
  · intro a ha; simp [p133] at ha; subst a; trivial
  · exact checked133
theorem derived133 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c133 := by
  apply localUnsat_implies_entails f133 [c130, c127, c120, c105, c131, c60, c132, c2, c93, c83] c133 unsat133 (by rfl) a
  have h0 : Entails.eval a c130 := derived130 a h
  have h1 : Entails.eval a c127 := derived127 a h
  have h2 : Entails.eval a c120 := derived120 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c131 := derived131 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c132 := derived132 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c134 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f134 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c120, some c105, some c127, some c130, some c47, some c133, some c64, some c30, some c2, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p134 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked134 : lratChecker f134 p134 = .success := by decide +kernel
theorem unsat134 : Unsatisfiable (PosFin 31) f134 := by
  apply lratCheckerSound f134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p134
  · intro a ha; simp [p134] at ha; subst a; trivial
  · exact checked134
theorem derived134 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c134 := by
  apply localUnsat_implies_entails f134 [c120, c105, c127, c130, c47, c133, c64, c30, c2] c134 unsat134 (by rfl) a
  have h0 : Entails.eval a c120 := derived120 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c127 := derived127 a h
  have h3 : Entails.eval a c130 := derived130 a h
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c133 := derived133 a h
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c135 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f135 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c134, some c110, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p135 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked135 : lratChecker f135 p135 = .success := by decide +kernel
theorem unsat135 : Unsatisfiable (PosFin 31) f135 := by
  apply lratCheckerSound f135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p135
  · intro a ha; simp [p135] at ha; subst a; trivial
  · exact checked135
theorem derived135 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c135 := by
  apply localUnsat_implies_entails f135 [c134, c110] c135 unsat135 (by rfl) a
  have h0 : Entails.eval a c134 := derived134 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c136 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f136 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c2, some c70, some c95, some c10, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p136 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked136 : lratChecker f136 p136 = .success := by decide +kernel
theorem unsat136 : Unsatisfiable (PosFin 31) f136 := by
  apply lratCheckerSound f136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p136
  · intro a ha; simp [p136] at ha; subst a; trivial
  · exact checked136
theorem derived136 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c136 := by
  apply localUnsat_implies_entails f136 [c135, c2, c70, c95, c10] c136 unsat136 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c137 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f137 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c136, some c17, some c52, some c105, some c34, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p137 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked137 : lratChecker f137 p137 = .success := by decide +kernel
theorem unsat137 : Unsatisfiable (PosFin 31) f137 := by
  apply lratCheckerSound f137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p137
  · intro a ha; simp [p137] at ha; subst a; trivial
  · exact checked137
theorem derived137 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c137 := by
  apply localUnsat_implies_entails f137 [c135, c136, c17, c52, c105, c34] c137 unsat137 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c136 := derived136 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c138 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f138 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c137, some c49, some c14, some c105, some c28, some c40, some c29, some c52, some c9, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p138 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked138 : lratChecker f138 p138 = .success := by decide +kernel
theorem unsat138 : Unsatisfiable (PosFin 31) f138 := by
  apply lratCheckerSound f138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p138
  · intro a ha; simp [p138] at ha; subst a; trivial
  · exact checked138
theorem derived138 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c138 := by
  apply localUnsat_implies_entails f138 [c135, c137, c49, c14, c105, c28, c40, c29, c52, c9] c138 unsat138 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c137 := derived137 a h
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c139 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f139 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c58, some c108, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p139 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked139 : lratChecker f139 p139 = .success := by decide +kernel
theorem unsat139 : Unsatisfiable (PosFin 31) f139 := by
  apply lratCheckerSound f139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p139
  · intro a ha; simp [p139] at ha; subst a; trivial
  · exact checked139
theorem derived139 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c139 := by
  apply localUnsat_implies_entails f139 [c41, c58, c108] c139 unsat139 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c140 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f140 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c138, some c51, some c139, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p140 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked140 : lratChecker f140 p140 = .success := by decide +kernel
theorem unsat140 : Unsatisfiable (PosFin 31) f140 := by
  apply lratCheckerSound f140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p140
  · intro a ha; simp [p140] at ha; subst a; trivial
  · exact checked140
theorem derived140 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c140 := by
  apply localUnsat_implies_entails f140 [c135, c138, c51, c139] c140 unsat140 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c138 := derived138 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c139 := derived139 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c141 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f141 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c140, some c138, some c67, some c16, some c76, some c2, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p141 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked141 : lratChecker f141 p141 = .success := by decide +kernel
theorem unsat141 : Unsatisfiable (PosFin 31) f141 := by
  apply lratCheckerSound f141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p141
  · intro a ha; simp [p141] at ha; subst a; trivial
  · exact checked141
theorem derived141 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c141 := by
  apply localUnsat_implies_entails f141 [c135, c140, c138, c67, c16, c76, c2] c141 unsat141 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c140 := derived140 a h
  have h2 : Entails.eval a c138 := derived138 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c142 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f142 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c134, some c140, some c141, some c108, some c37, some c2, some c24, some c45, some c96, some c77, some c101, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p142 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked142 : lratChecker f142 p142 = .success := by decide +kernel
theorem unsat142 : Unsatisfiable (PosFin 31) f142 := by
  apply lratCheckerSound f142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p142
  · intro a ha; simp [p142] at ha; subst a; trivial
  · exact checked142
theorem derived142 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c142 := by
  apply localUnsat_implies_entails f142 [c135, c134, c140, c141, c108, c37, c2, c24, c45, c96, c77, c101] c142 unsat142 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c134 := derived134 a h
  have h2 : Entails.eval a c140 := derived140 a h
  have h3 : Entails.eval a c141 := derived141 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c143 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f143 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c48, some c29, some c105, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p143 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked143 : lratChecker f143 p143 = .success := by decide +kernel
theorem unsat143 : Unsatisfiable (PosFin 31) f143 := by
  apply lratCheckerSound f143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p143
  · intro a ha; simp [p143] at ha; subst a; trivial
  · exact checked143
theorem derived143 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c143 := by
  apply localUnsat_implies_entails f143 [c48, c29, c105] c143 unsat143 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c144 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f144 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c142, some c143, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p144 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked144 : lratChecker f144 p144 = .success := by decide +kernel
theorem unsat144 : Unsatisfiable (PosFin 31) f144 := by
  apply lratCheckerSound f144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p144
  · intro a ha; simp [p144] at ha; subst a; trivial
  · exact checked144
theorem derived144 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c144 := by
  apply localUnsat_implies_entails f144 [c142, c143] c144 unsat144 (by rfl) a
  have h0 : Entails.eval a c142 := derived142 a h
  have h1 : Entails.eval a c143 := derived143 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c145 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f145 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c138, some c140, some c144, some c72, some c2, some c52, some c3, some c73, some c6, some c67, some c75, some c108, some c91, some c87, some c42, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p145 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked145 : lratChecker f145 p145 = .success := by decide +kernel
theorem unsat145 : Unsatisfiable (PosFin 31) f145 := by
  apply lratCheckerSound f145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p145
  · intro a ha; simp [p145] at ha; subst a; trivial
  · exact checked145
theorem derived145 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c145 := by
  apply localUnsat_implies_entails f145 [c135, c138, c140, c144, c72, c2, c52, c3, c73, c6, c67, c75, c108, c91, c87, c42] c145 unsat145 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c138 := derived138 a h
  have h2 : Entails.eval a c140 := derived140 a h
  have h3 : Entails.eval a c144 := derived144 a h
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c91 := h 90 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c146 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f146 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c134, some c145, some c56, some c54, some c125, some c21, some c1, some c43, some c51, some c38, some c73, some c108, some c85, some c81, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p146 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked146 : lratChecker f146 p146 = .success := by decide +kernel
theorem unsat146 : Unsatisfiable (PosFin 31) f146 := by
  apply lratCheckerSound f146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p146
  · intro a ha; simp [p146] at ha; subst a; trivial
  · exact checked146
theorem derived146 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c146 := by
  apply localUnsat_implies_entails f146 [c135, c134, c145, c56, c54, c125, c21, c1, c43, c51, c38, c73, c108, c85, c81] c146 unsat146 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c134 := derived134 a h
  have h2 : Entails.eval a c145 := derived145 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c125 := derived125 a h
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c85 := h 84 (by decide)
  have h14 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c147 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f147 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c134, some c135, some c145, some c146, some c2, some c72, some c97, some c70, some c96, some c36, some c107, some c104, some c8, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p147 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked147 : lratChecker f147 p147 = .success := by decide +kernel
theorem unsat147 : Unsatisfiable (PosFin 31) f147 := by
  apply lratCheckerSound f147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p147
  · intro a ha; simp [p147] at ha; subst a; trivial
  · exact checked147
theorem derived147 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c147 := by
  apply localUnsat_implies_entails f147 [c134, c135, c145, c146, c2, c72, c97, c70, c96, c36, c107, c104, c8] c147 unsat147 (by rfl) a
  have h0 : Entails.eval a c134 := derived134 a h
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c145 := derived145 a h
  have h3 : Entails.eval a c146 := derived146 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c148 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f148 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c57, some c40, some c105, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p148 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked148 : lratChecker f148 p148 = .success := by decide +kernel
theorem unsat148 : Unsatisfiable (PosFin 31) f148 := by
  apply lratCheckerSound f148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p148
  · intro a ha; simp [p148] at ha; subst a; trivial
  · exact checked148
theorem derived148 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c148 := by
  apply localUnsat_implies_entails f148 [c57, c40, c105] c148 unsat148 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c149 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f149 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c145, some c146, some c147, some c51, some c49, some c148, some c97, some c42, some c4, some c68, some c98, some c90, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p149 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked149 : lratChecker f149 p149 = .success := by decide +kernel
theorem unsat149 : Unsatisfiable (PosFin 31) f149 := by
  apply lratCheckerSound f149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p149
  · intro a ha; simp [p149] at ha; subst a; trivial
  · exact checked149
theorem derived149 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c149 := by
  apply localUnsat_implies_entails f149 [c135, c145, c146, c147, c51, c49, c148, c97, c42, c4, c68, c98, c90] c149 unsat149 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c145 := derived145 a h
  have h2 : Entails.eval a c146 := derived146 a h
  have h3 : Entails.eval a c147 := derived147 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c148 := derived148 a h
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c150 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f150 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c149, some c135, some c145, some c50, some c56, some c97, some c5, some c99, some c100, some c89, some c98, some c105, some c68, some c66, some c43, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p150 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked150 : lratChecker f150 p150 = .success := by decide +kernel
theorem unsat150 : Unsatisfiable (PosFin 31) f150 := by
  apply lratCheckerSound f150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p150
  · intro a ha; simp [p150] at ha; subst a; trivial
  · exact checked150
theorem derived150 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c150 := by
  apply localUnsat_implies_entails f150 [c149, c135, c145, c50, c56, c97, c5, c99, c100, c89, c98, c105, c68, c66, c43] c150 unsat150 (by rfl) a
  have h0 : Entails.eval a c149 := derived149 a h
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c145 := derived145 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c151 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f151 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c149, some c145, some c135, some c50, some c150, some c148, some c13, some c11, some c108, some c54, some c26, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p151 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked151 : lratChecker f151 p151 = .success := by decide +kernel
theorem unsat151 : Unsatisfiable (PosFin 31) f151 := by
  apply lratCheckerSound f151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p151
  · intro a ha; simp [p151] at ha; subst a; trivial
  · exact checked151
theorem derived151 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c151 := by
  apply localUnsat_implies_entails f151 [c149, c145, c135, c50, c150, c148, c13, c11, c108, c54, c26] c151 unsat151 (by rfl) a
  have h0 : Entails.eval a c149 := derived149 a h
  have h1 : Entails.eval a c145 := derived145 a h
  have h2 : Entails.eval a c135 := derived135 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c150 := derived150 a h
  have h5 : Entails.eval a c148 := derived148 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c152 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f152 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c145, some c149, some c135, some c151, some c1, some c43, some c108, some c37, some c88, some c54, some c2, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p152 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked152 : lratChecker f152 p152 = .success := by decide +kernel
theorem unsat152 : Unsatisfiable (PosFin 31) f152 := by
  apply lratCheckerSound f152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p152
  · intro a ha; simp [p152] at ha; subst a; trivial
  · exact checked152
theorem derived152 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c152 := by
  apply localUnsat_implies_entails f152 [c145, c149, c135, c151, c1, c43, c108, c37, c88, c54, c2] c152 unsat152 (by rfl) a
  have h0 : Entails.eval a c145 := derived145 a h
  have h1 : Entails.eval a c149 := derived149 a h
  have h2 : Entails.eval a c135 := derived135 a h
  have h3 : Entails.eval a c151 := derived151 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c153 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f153 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c151, some c135, some c149, some c125, some c2, some c71, some c96, some c12, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p153 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked153 : lratChecker f153 p153 = .success := by decide +kernel
theorem unsat153 : Unsatisfiable (PosFin 31) f153 := by
  apply lratCheckerSound f153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p153
  · intro a ha; simp [p153] at ha; subst a; trivial
  · exact checked153
theorem derived153 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c153 := by
  apply localUnsat_implies_entails f153 [c151, c135, c149, c125, c2, c71, c96, c12] c153 unsat153 (by rfl) a
  have h0 : Entails.eval a c151 := derived151 a h
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c149 := derived149 a h
  have h3 : Entails.eval a c125 := derived125 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c154 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f154 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c152, some c153, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p154 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked154 : lratChecker f154 p154 = .success := by decide +kernel
theorem unsat154 : Unsatisfiable (PosFin 31) f154 := by
  apply lratCheckerSound f154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p154
  · intro a ha; simp [p154] at ha; subst a; trivial
  · exact checked154
theorem derived154 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c154 := by
  apply localUnsat_implies_entails f154 [c152, c153] c154 unsat154 (by rfl) a
  have h0 : Entails.eval a c152 := derived152 a h
  have h1 : Entails.eval a c153 := derived153 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c155 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f155 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c154, some c145, some c135, some c56, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p155 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked155 : lratChecker f155 p155 = .success := by decide +kernel
theorem unsat155 : Unsatisfiable (PosFin 31) f155 := by
  apply lratCheckerSound f155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p155
  · intro a ha; simp [p155] at ha; subst a; trivial
  · exact checked155
theorem derived155 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c155 := by
  apply localUnsat_implies_entails f155 [c154, c145, c135, c56] c155 unsat155 (by rfl) a
  have h0 : Entails.eval a c154 := derived154 a h
  have h1 : Entails.eval a c145 := derived145 a h
  have h2 : Entails.eval a c135 := derived135 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c156 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f156 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c154, some c135, some c145, some c97, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p156 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked156 : lratChecker f156 p156 = .success := by decide +kernel
theorem unsat156 : Unsatisfiable (PosFin 31) f156 := by
  apply lratCheckerSound f156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p156
  · intro a ha; simp [p156] at ha; subst a; trivial
  · exact checked156
theorem derived156 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c156 := by
  apply localUnsat_implies_entails f156 [c154, c135, c145, c97] c156 unsat156 (by rfl) a
  have h0 : Entails.eval a c154 := derived154 a h
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c145 := derived145 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c157 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f157 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c156, some c155, some c151, some c2]
def p157 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked157 : lratChecker f157 p157 = .success := by decide +kernel
theorem unsat157 : Unsatisfiable (PosFin 31) f157 := by
  apply lratCheckerSound f157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p157
  · intro a ha; simp [p157] at ha; subst a; trivial
  · exact checked157
theorem derived157 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c157 := by
  apply localUnsat_implies_entails f157 [c156, c155, c151, c2] c157 unsat157 (by rfl) a
  have h0 : Entails.eval a c156 := derived156 a h
  have h1 : Entails.eval a c155 := derived155 a h
  have h2 : Entails.eval a c151 := derived151 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived157

end CochromaticTwenty.Certificates.Z12Direct_5_5_3
