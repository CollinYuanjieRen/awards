import MerLeanExperiment.Certificates.Z12Direct_5_5_2.Inputs

/-! Generated from the actual pinned z12direct_5_5_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c97 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f97 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c27, some c91, some c13, some c16, some c28, some c39, some c35, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p97 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked97 : lratChecker f97 p97 = .success := by decide +kernel
theorem unsat97 : Unsatisfiable (PosFin 31) f97 := by
  apply lratCheckerSound f97 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p97
  · intro a ha; simp [p97] at ha; subst a; trivial
  · exact checked97
theorem derived97 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c97 := by
  apply localUnsat_implies_entails f97 [c27, c91, c13, c16, c28, c39, c35] c97 unsat97 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c98 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f98 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c27, some c91, some c97, some c32, some c47, some c12, some c7, some c56, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p98 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked98 : lratChecker f98 p98 = .success := by decide +kernel
theorem unsat98 : Unsatisfiable (PosFin 31) f98 := by
  apply lratCheckerSound f98 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p98
  · intro a ha; simp [p98] at ha; subst a; trivial
  · exact checked98
theorem derived98 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c98 := by
  apply localUnsat_implies_entails f98 [c27, c91, c97, c32, c47, c12, c7, c56] c98 unsat98 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c97 := derived97 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c99 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f99 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c98, some c27, some c91, some c93, some c26, some c32, some c47, some c12, some c7, some c75, some c74, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p99 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked99 : lratChecker f99 p99 = .success := by decide +kernel
theorem unsat99 : Unsatisfiable (PosFin 31) f99 := by
  apply lratCheckerSound f99 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p99
  · intro a ha; simp [p99] at ha; subst a; trivial
  · exact checked99
theorem derived99 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c99 := by
  apply localUnsat_implies_entails f99 [c98, c27, c91, c93, c26, c32, c47, c12, c7, c75, c74] c99 unsat99 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c100 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f100 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c99, some c16, some c27, some c91, some c2, some c67, some c48, some c45, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p100 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked100 : lratChecker f100 p100 = .success := by decide +kernel
theorem unsat100 : Unsatisfiable (PosFin 31) f100 := by
  apply lratCheckerSound f100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p100
  · intro a ha; simp [p100] at ha; subst a; trivial
  · exact checked100
theorem derived100 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c100 := by
  apply localUnsat_implies_entails f100 [c99, c16, c27, c91, c2, c67, c48, c45] c100 unsat100 (by rfl) a
  have h0 : Entails.eval a c99 := derived99 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c101 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f101 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c99, some c100, some c34, some c35, some c28, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p101 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked101 : lratChecker f101 p101 = .success := by decide +kernel
theorem unsat101 : Unsatisfiable (PosFin 31) f101 := by
  apply lratCheckerSound f101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p101
  · intro a ha; simp [p101] at ha; subst a; trivial
  · exact checked101
theorem derived101 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c101 := by
  apply localUnsat_implies_entails f101 [c99, c100, c34, c35, c28] c101 unsat101 (by rfl) a
  have h0 : Entails.eval a c99 := derived99 a h
  have h1 : Entails.eval a c100 := derived100 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c102 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f102 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c101, some c85, some c59, some c91, some c15, some c87, some c26, some c35, some c66, some c37, some c38, some c83, some c84, some c53, some c54, some c58, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p102 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked102 : lratChecker f102 p102 = .success := by decide +kernel
theorem unsat102 : Unsatisfiable (PosFin 31) f102 := by
  apply lratCheckerSound f102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p102
  · intro a ha; simp [p102] at ha; subst a; trivial
  · exact checked102
theorem derived102 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c102 := by
  apply localUnsat_implies_entails f102 [c101, c85, c59, c91, c15, c87, c26, c35, c66, c37, c38, c83, c84, c53, c54, c58] c102 unsat102 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c103 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f103 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c101, some c85, some c59, some c91, some c15, some c102, some c52, some c30, some c68, some c33, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p103 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked103 : lratChecker f103 p103 = .success := by decide +kernel
theorem unsat103 : Unsatisfiable (PosFin 31) f103 := by
  apply lratCheckerSound f103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p103
  · intro a ha; simp [p103] at ha; subst a; trivial
  · exact checked103
theorem derived103 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c103 := by
  apply localUnsat_implies_entails f103 [c101, c85, c59, c91, c15, c102, c52, c30, c68, c33] c103 unsat103 (by rfl) a
  have h0 : Entails.eval a c101 := derived101 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c102 := derived102 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c104 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f104 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c26, some c101, some c85, some c59, some c91, some c87, some c103, some c31, some c46, some c11, some c6, some c65, some c81, some c89, some c17, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p104 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked104 : lratChecker f104 p104 = .success := by decide +kernel
theorem unsat104 : Unsatisfiable (PosFin 31) f104 := by
  apply lratCheckerSound f104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p104
  · intro a ha; simp [p104] at ha; subst a; trivial
  · exact checked104
theorem derived104 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c104 := by
  apply localUnsat_implies_entails f104 [c26, c101, c85, c59, c91, c87, c103, c31, c46, c11, c6, c65, c81, c89, c17] c104 unsat104 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c101 := derived101 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c103 := derived103 a h
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c105 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f105 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c104, some c92, some c27, some c62, some c85, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p105 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked105 : lratChecker f105 p105 = .success := by decide +kernel
theorem unsat105 : Unsatisfiable (PosFin 31) f105 := by
  apply lratCheckerSound f105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p105
  · intro a ha; simp [p105] at ha; subst a; trivial
  · exact checked105
theorem derived105 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c105 := by
  apply localUnsat_implies_entails f105 [c104, c92, c27, c62, c85] c105 unsat105 (by rfl) a
  have h0 : Entails.eval a c104 := derived104 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c106 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f106 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c105, some c91, some c104, some c92, some c63, some c85, some c70, some c50, some c51, some c77, some c3, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p106 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked106 : lratChecker f106 p106 = .success := by decide +kernel
theorem unsat106 : Unsatisfiable (PosFin 31) f106 := by
  apply lratCheckerSound f106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p106
  · intro a ha; simp [p106] at ha; subst a; trivial
  · exact checked106
theorem derived106 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c106 := by
  apply localUnsat_implies_entails f106 [c105, c91, c104, c92, c63, c85, c70, c50, c51, c77, c3] c106 unsat106 (by rfl) a
  have h0 : Entails.eval a c105 := derived105 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c104 := derived104 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c107 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f107 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c91, some c19, some c22, some c77, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p107 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked107 : lratChecker f107 p107 = .success := by decide +kernel
theorem unsat107 : Unsatisfiable (PosFin 31) f107 := by
  apply lratCheckerSound f107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p107
  · intro a ha; simp [p107] at ha; subst a; trivial
  · exact checked107
theorem derived107 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c107 := by
  apply localUnsat_implies_entails f107 [c91, c19, c22, c77] c107 unsat107 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c108 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f108 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c104, some c105, some c107, some c63, some c91, some c92, some c106, some c41, some c42, some c36, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p108 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked108 : lratChecker f108 p108 = .success := by decide +kernel
theorem unsat108 : Unsatisfiable (PosFin 31) f108 := by
  apply lratCheckerSound f108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p108
  · intro a ha; simp [p108] at ha; subst a; trivial
  · exact checked108
theorem derived108 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c108 := by
  apply localUnsat_implies_entails f108 [c104, c105, c107, c63, c91, c92, c106, c41, c42, c36] c108 unsat108 (by rfl) a
  have h0 : Entails.eval a c104 := derived104 a h
  have h1 : Entails.eval a c105 := derived105 a h
  have h2 : Entails.eval a c107 := derived107 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c106 := derived106 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c109 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f109 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c104, some c105, some c107, some c63, some c85, some c70, some c108, some c77, some c97, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p109 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked109 : lratChecker f109 p109 = .success := by decide +kernel
theorem unsat109 : Unsatisfiable (PosFin 31) f109 := by
  apply lratCheckerSound f109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p109
  · intro a ha; simp [p109] at ha; subst a; trivial
  · exact checked109
theorem derived109 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c109 := by
  apply localUnsat_implies_entails f109 [c104, c105, c107, c63, c85, c70, c108, c77, c97] c109 unsat109 (by rfl) a
  have h0 : Entails.eval a c104 := derived104 a h
  have h1 : Entails.eval a c105 := derived105 a h
  have h2 : Entails.eval a c107 := derived107 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c108 := derived108 a h
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c97 := derived97 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c110 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f110 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c109, some c86, some c27, some c70, some c91, some c61, some c92, some c77, some c97, some c41, some c50, some c12, some c7, some c56, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p110 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked110 : lratChecker f110 p110 = .success := by decide +kernel
theorem unsat110 : Unsatisfiable (PosFin 31) f110 := by
  apply lratCheckerSound f110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p110
  · intro a ha; simp [p110] at ha; subst a; trivial
  · exact checked110
theorem derived110 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c110 := by
  apply localUnsat_implies_entails f110 [c109, c86, c27, c70, c91, c61, c92, c77, c97, c41, c50, c12, c7, c56] c110 unsat110 (by rfl) a
  have h0 : Entails.eval a c109 := derived109 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c97 := derived97 a h
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c7 := h 6 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c111 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f111 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c110, some c85, some c109, some c86, some c20, some c22, some c71, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p111 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked111 : lratChecker f111 p111 = .success := by decide +kernel
theorem unsat111 : Unsatisfiable (PosFin 31) f111 := by
  apply lratCheckerSound f111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p111
  · intro a ha; simp [p111] at ha; subst a; trivial
  · exact checked111
theorem derived111 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c111 := by
  apply localUnsat_implies_entails f111 [c110, c85, c109, c86, c20, c22, c71] c111 unsat111 (by rfl) a
  have h0 : Entails.eval a c110 := derived110 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c109 := derived109 a h
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c112 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f112 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c109, some c110, some c86, some c111, some c60, some c21, some c71, some c91, some c85, some c41, some c50, some c11, some c6, some c55, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p112 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked112 : lratChecker f112 p112 = .success := by decide +kernel
theorem unsat112 : Unsatisfiable (PosFin 31) f112 := by
  apply lratCheckerSound f112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p112
  · intro a ha; simp [p112] at ha; subst a; trivial
  · exact checked112
theorem derived112 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c112 := by
  apply localUnsat_implies_entails f112 [c109, c110, c86, c111, c60, c21, c71, c91, c85, c41, c50, c11, c6, c55] c112 unsat112 (by rfl) a
  have h0 : Entails.eval a c109 := derived109 a h
  have h1 : Entails.eval a c110 := derived110 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c111 := derived111 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c113 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f113 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c109, some c86, some c110, some c85, some c111, some c60, some c91, some c21, some c71, some c112, some c14, some c15, some c30, some c37, some c35, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p113 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked113 : lratChecker f113 p113 = .success := by decide +kernel
theorem unsat113 : Unsatisfiable (PosFin 31) f113 := by
  apply lratCheckerSound f113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p113
  · intro a ha; simp [p113] at ha; subst a; trivial
  · exact checked113
theorem derived113 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c113 := by
  apply localUnsat_implies_entails f113 [c109, c86, c110, c85, c111, c60, c91, c21, c71, c112, c14, c15, c30, c37, c35] c113 unsat113 (by rfl) a
  have h0 : Entails.eval a c109 := derived109 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c110 := derived110 a h
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c111 := derived111 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c112 := derived112 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c114 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f114 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c95, some c21, some c2, some c69, some c96, some c4, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p114 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked114 : lratChecker f114 p114 = .success := by decide +kernel
theorem unsat114 : Unsatisfiable (PosFin 31) f114 := by
  apply lratCheckerSound f114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p114
  · intro a ha; simp [p114] at ha; subst a; trivial
  · exact checked114
theorem derived114 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c114 := by
  apply localUnsat_implies_entails f114 [c95, c21, c2, c69, c96, c4] c114 unsat114 (by rfl) a
  have h0 : Entails.eval a c95 := h 94 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c115 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f115 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c14, some c62, some c114, some c43, some c44, some c29, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p115 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked115 : lratChecker f115 p115 = .success := by decide +kernel
theorem unsat115 : Unsatisfiable (PosFin 31) f115 := by
  apply lratCheckerSound f115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p115
  · intro a ha; simp [p115] at ha; subst a; trivial
  · exact checked115
theorem derived115 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c115 := by
  apply localUnsat_implies_entails f115 [c113, c14, c62, c114, c43, c44, c29] c115 unsat115 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c114 := derived114 a h
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c116 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f116 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c78, some c23, some c24, some c60, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p116 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked116 : lratChecker f116 p116 = .success := by decide +kernel
theorem unsat116 : Unsatisfiable (PosFin 31) f116 := by
  apply lratCheckerSound f116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p116
  · intro a ha; simp [p116] at ha; subst a; trivial
  · exact checked116
theorem derived116 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c116 := by
  apply localUnsat_implies_entails f116 [c113, c78, c23, c24, c60] c116 unsat116 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c117 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f117 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c22, some c116, some c21, some c95, some c115, some c41, some c50, some c10, some c5, some c75, some c73, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p117 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked117 : lratChecker f117 p117 = .success := by decide +kernel
theorem unsat117 : Unsatisfiable (PosFin 31) f117 := by
  apply lratCheckerSound f117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p117
  · intro a ha; simp [p117] at ha; subst a; trivial
  · exact checked117
theorem derived117 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c117 := by
  apply localUnsat_implies_entails f117 [c113, c22, c116, c21, c95, c115, c41, c50, c10, c5, c75, c73] c117 unsat117 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c116 := derived116 a h
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c115 := derived115 a h
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c118 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f118 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c117, some c21, some c95, some c18, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p118 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked118 : lratChecker f118 p118 = .success := by decide +kernel
theorem unsat118 : Unsatisfiable (PosFin 31) f118 := by
  apply lratCheckerSound f118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p118
  · intro a ha; simp [p118] at ha; subst a; trivial
  · exact checked118
theorem derived118 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c118 := by
  apply localUnsat_implies_entails f118 [c113, c117, c21, c95, c18] c118 unsat118 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c117 := derived117 a h
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c119 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f119 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c117, some c118, some c79, some c116, some c18, some c20, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p119 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked119 : lratChecker f119 p119 = .success := by decide +kernel
theorem unsat119 : Unsatisfiable (PosFin 31) f119 := by
  apply lratCheckerSound f119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p119
  · intro a ha; simp [p119] at ha; subst a; trivial
  · exact checked119
theorem derived119 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c119 := by
  apply localUnsat_implies_entails f119 [c113, c117, c118, c79, c116, c18, c20] c119 unsat119 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c117 := derived117 a h
  have h2 : Entails.eval a c118 := derived118 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c116 := derived116 a h
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c120 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f120 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c119, some c91, some c107, some c20, some c94, some c22, some c18, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p120 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked120 : lratChecker f120 p120 = .success := by decide +kernel
theorem unsat120 : Unsatisfiable (PosFin 31) f120 := by
  apply lratCheckerSound f120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p120
  · intro a ha; simp [p120] at ha; subst a; trivial
  · exact checked120
theorem derived120 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c120 := by
  apply localUnsat_implies_entails f120 [c113, c119, c91, c107, c20, c94, c22, c18] c120 unsat120 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c119 := derived119 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c107 := derived107 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c121 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f121 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c120, some c86, some c91, some c107, some c59, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p121 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked121 : lratChecker f121 p121 = .success := by decide +kernel
theorem unsat121 : Unsatisfiable (PosFin 31) f121 := by
  apply lratCheckerSound f121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p121
  · intro a ha; simp [p121] at ha; subst a; trivial
  · exact checked121
theorem derived121 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c121 := by
  apply localUnsat_implies_entails f121 [c120, c86, c91, c107, c59] c121 unsat121 (by rfl) a
  have h0 : Entails.eval a c120 := derived120 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c107 := derived107 a h
  have h4 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c122 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f122 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c120, some c86, some c121, some c24, some c62, some c78, some c92, some c59, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p122 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked122 : lratChecker f122 p122 = .success := by decide +kernel
theorem unsat122 : Unsatisfiable (PosFin 31) f122 := by
  apply lratCheckerSound f122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p122
  · intro a ha; simp [p122] at ha; subst a; trivial
  · exact checked122
theorem derived122 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c122 := by
  apply localUnsat_implies_entails f122 [c113, c120, c86, c121, c24, c62, c78, c92, c59] c122 unsat122 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c120 := derived120 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c121 := derived121 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c123 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f123 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c122, some c85, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p123 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked123 : lratChecker f123 p123 = .success := by decide +kernel
theorem unsat123 : Unsatisfiable (PosFin 31) f123 := by
  apply lratCheckerSound f123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p123
  · intro a ha; simp [p123] at ha; subst a; trivial
  · exact checked123
theorem derived123 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c123 := by
  apply localUnsat_implies_entails f123 [c122, c85] c123 unsat123 (by rfl) a
  have h0 : Entails.eval a c122 := derived122 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c124 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f124 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c123, some c64, some c92, some c116, some c61, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p124 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked124 : lratChecker f124 p124 = .success := by decide +kernel
theorem unsat124 : Unsatisfiable (PosFin 31) f124 := by
  apply lratCheckerSound f124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p124
  · intro a ha; simp [p124] at ha; subst a; trivial
  · exact checked124
theorem derived124 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c124 := by
  apply localUnsat_implies_entails f124 [c123, c64, c92, c116, c61] c124 unsat124 (by rfl) a
  have h0 : Entails.eval a c123 := derived123 a h
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c116 := derived116 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c125 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f125 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c123, some c113, some c122, some c23, some c72, some c124, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p125 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked125 : lratChecker f125 p125 = .success := by decide +kernel
theorem unsat125 : Unsatisfiable (PosFin 31) f125 := by
  apply lratCheckerSound f125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p125
  · intro a ha; simp [p125] at ha; subst a; trivial
  · exact checked125
theorem derived125 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c125 := by
  apply localUnsat_implies_entails f125 [c123, c113, c122, c23, c72, c124] c125 unsat125 (by rfl) a
  have h0 : Entails.eval a c123 := derived123 a h
  have h1 : Entails.eval a c113 := derived113 a h
  have h2 : Entails.eval a c122 := derived122 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c124 := derived124 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c126 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f126 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c125, some c91, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p126 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked126 : lratChecker f126 p126 = .success := by decide +kernel
theorem unsat126 : Unsatisfiable (PosFin 31) f126 := by
  apply lratCheckerSound f126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p126
  · intro a ha; simp [p126] at ha; subst a; trivial
  · exact checked126
theorem derived126 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c126 := by
  apply localUnsat_implies_entails f126 [c125, c91] c126 unsat126 (by rfl) a
  have h0 : Entails.eval a c125 := derived125 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c127 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f127 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c126, some c123, some c113, some c122, some c25, some c61, some c72, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p127 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked127 : lratChecker f127 p127 = .success := by decide +kernel
theorem unsat127 : Unsatisfiable (PosFin 31) f127 := by
  apply lratCheckerSound f127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p127
  · intro a ha; simp [p127] at ha; subst a; trivial
  · exact checked127
theorem derived127 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c127 := by
  apply localUnsat_implies_entails f127 [c126, c123, c113, c122, c25, c61, c72] c127 unsat127 (by rfl) a
  have h0 : Entails.eval a c126 := derived126 a h
  have h1 : Entails.eval a c123 := derived123 a h
  have h2 : Entails.eval a c113 := derived113 a h
  have h3 : Entails.eval a c122 := derived122 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c128 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f128 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c127, some c92, some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p128 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked128 : lratChecker f128 p128 = .success := by decide +kernel
theorem unsat128 : Unsatisfiable (PosFin 31) f128 := by
  apply lratCheckerSound f128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p128
  · intro a ha; simp [p128] at ha; subst a; trivial
  · exact checked128
theorem derived128 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c128 := by
  apply localUnsat_implies_entails f128 [c127, c92] c128 unsat128 (by rfl) a
  have h0 : Entails.eval a c127 := derived127 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c129 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f129 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c127, some c125, some c122, some c63, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p129 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked129 : lratChecker f129 p129 = .success := by decide +kernel
theorem unsat129 : Unsatisfiable (PosFin 31) f129 := by
  apply lratCheckerSound f129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p129
  · intro a ha; simp [p129] at ha; subst a; trivial
  · exact checked129
theorem derived129 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c129 := by
  apply localUnsat_implies_entails f129 [c127, c125, c122, c63] c129 unsat129 (by rfl) a
  have h0 : Entails.eval a c127 := derived127 a h
  have h1 : Entails.eval a c125 := derived125 a h
  have h2 : Entails.eval a c122 := derived122 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c130 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f130 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c127, some c126, some c113, some c76, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p130 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked130 : lratChecker f130 p130 = .success := by decide +kernel
theorem unsat130 : Unsatisfiable (PosFin 31) f130 := by
  apply lratCheckerSound f130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p130
  · intro a ha; simp [p130] at ha; subst a; trivial
  · exact checked130
theorem derived130 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c130 := by
  apply localUnsat_implies_entails f130 [c127, c126, c113, c76] c130 unsat130 (by rfl) a
  have h0 : Entails.eval a c127 := derived127 a h
  have h1 : Entails.eval a c126 := derived126 a h
  have h2 : Entails.eval a c113 := derived113 a h
  have h3 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c131 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f131 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c129, some c126, some c123, some c88, some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p131 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked131 : lratChecker f131 p131 = .success := by decide +kernel
theorem unsat131 : Unsatisfiable (PosFin 31) f131 := by
  apply lratCheckerSound f131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p131
  · intro a ha; simp [p131] at ha; subst a; trivial
  · exact checked131
theorem derived131 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c131 := by
  apply localUnsat_implies_entails f131 [c129, c126, c123, c88] c131 unsat131 (by rfl) a
  have h0 : Entails.eval a c129 := derived129 a h
  have h1 : Entails.eval a c126 := derived126 a h
  have h2 : Entails.eval a c123 := derived123 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c132 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f132 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c130, some c131, some c113, some c18, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p132 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked132 : lratChecker f132 p132 = .success := by decide +kernel
theorem unsat132 : Unsatisfiable (PosFin 31) f132 := by
  apply lratCheckerSound f132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p132
  · intro a ha; simp [p132] at ha; subst a; trivial
  · exact checked132
theorem derived132 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c132 := by
  apply localUnsat_implies_entails f132 [c130, c131, c113, c18] c132 unsat132 (by rfl) a
  have h0 : Entails.eval a c130 := derived130 a h
  have h1 : Entails.eval a c131 := derived131 a h
  have h2 : Entails.eval a c113 := derived113 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c133 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f133 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c131, some c128, some c113, some c130, some c81, some c80, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p133 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked133 : lratChecker f133 p133 = .success := by decide +kernel
theorem unsat133 : Unsatisfiable (PosFin 31) f133 := by
  apply lratCheckerSound f133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p133
  · intro a ha; simp [p133] at ha; subst a; trivial
  · exact checked133
theorem derived133 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c133 := by
  apply localUnsat_implies_entails f133 [c131, c128, c113, c130, c81, c80] c133 unsat133 (by rfl) a
  have h0 : Entails.eval a c131 := derived131 a h
  have h1 : Entails.eval a c128 := derived128 a h
  have h2 : Entails.eval a c113 := derived113 a h
  have h3 : Entails.eval a c130 := derived130 a h
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c134 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f134 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c129, some c126, some c132, some c40, some c49, some c9, some c3, some c133, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p134 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked134 : lratChecker f134 p134 = .success := by decide +kernel
theorem unsat134 : Unsatisfiable (PosFin 31) f134 := by
  apply lratCheckerSound f134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p134
  · intro a ha; simp [p134] at ha; subst a; trivial
  · exact checked134
theorem derived134 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c134 := by
  apply localUnsat_implies_entails f134 [c129, c126, c132, c40, c49, c9, c3, c133] c134 unsat134 (by rfl) a
  have h0 : Entails.eval a c129 := derived129 a h
  have h1 : Entails.eval a c126 := derived126 a h
  have h2 : Entails.eval a c132 := derived132 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c133 := derived133 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c135 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f135 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c134, some c126, some c132, some c13, some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p135 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked135 : lratChecker f135 p135 = .success := by decide +kernel
theorem unsat135 : Unsatisfiable (PosFin 31) f135 := by
  apply lratCheckerSound f135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p135
  · intro a ha; simp [p135] at ha; subst a; trivial
  · exact checked135
theorem derived135 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c135 := by
  apply localUnsat_implies_entails f135 [c134, c126, c132, c13] c135 unsat135 (by rfl) a
  have h0 : Entails.eval a c134 := derived134 a h
  have h1 : Entails.eval a c126 := derived126 a h
  have h2 : Entails.eval a c132 := derived132 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c136 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f136 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c132, some c126, some c135, some c130, some c131, some c84, some c1, some c3, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p136 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked136 : lratChecker f136 p136 = .success := by decide +kernel
theorem unsat136 : Unsatisfiable (PosFin 31) f136 := by
  apply lratCheckerSound f136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p136
  · intro a ha; simp [p136] at ha; subst a; trivial
  · exact checked136
theorem derived136 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c136 := by
  apply localUnsat_implies_entails f136 [c132, c126, c135, c130, c131, c84, c1, c3] c136 unsat136 (by rfl) a
  have h0 : Entails.eval a c132 := derived132 a h
  have h1 : Entails.eval a c126 := derived126 a h
  have h2 : Entails.eval a c135 := derived135 a h
  have h3 : Entails.eval a c130 := derived130 a h
  have h4 : Entails.eval a c131 := derived131 a h
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c137 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f137 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c113, some c131, some c135, some c128, some c82, some c136, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p137 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked137 : lratChecker f137 p137 = .success := by decide +kernel
theorem unsat137 : Unsatisfiable (PosFin 31) f137 := by
  apply lratCheckerSound f137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p137
  · intro a ha; simp [p137] at ha; subst a; trivial
  · exact checked137
theorem derived137 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c137 := by
  apply localUnsat_implies_entails f137 [c113, c131, c135, c128, c82, c136] c137 unsat137 (by rfl) a
  have h0 : Entails.eval a c113 := derived113 a h
  have h1 : Entails.eval a c131 := derived131 a h
  have h2 : Entails.eval a c135 := derived135 a h
  have h3 : Entails.eval a c128 := derived128 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c136 := derived136 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c138 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f138 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c137, some c126, some c129, some c8, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p138 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked138 : lratChecker f138 p138 = .success := by decide +kernel
theorem unsat138 : Unsatisfiable (PosFin 31) f138 := by
  apply lratCheckerSound f138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p138
  · intro a ha; simp [p138] at ha; subst a; trivial
  · exact checked138
theorem derived138 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c138 := by
  apply localUnsat_implies_entails f138 [c137, c126, c129, c8] c138 unsat138 (by rfl) a
  have h0 : Entails.eval a c137 := derived137 a h
  have h1 : Entails.eval a c126 := derived126 a h
  have h2 : Entails.eval a c129 := derived129 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c139 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f139 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c137, some c134, some c132, some c44, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p139 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked139 : lratChecker f139 p139 = .success := by decide +kernel
theorem unsat139 : Unsatisfiable (PosFin 31) f139 := by
  apply lratCheckerSound f139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p139
  · intro a ha; simp [p139] at ha; subst a; trivial
  · exact checked139
theorem derived139 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c139 := by
  apply localUnsat_implies_entails f139 [c137, c134, c132, c44] c139 unsat139 (by rfl) a
  have h0 : Entails.eval a c137 := derived137 a h
  have h1 : Entails.eval a c134 := derived134 a h
  have h2 : Entails.eval a c132 := derived132 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c140 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f140 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c137, some c126, some c132, some c9, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p140 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked140 : lratChecker f140 p140 = .success := by decide +kernel
theorem unsat140 : Unsatisfiable (PosFin 31) f140 := by
  apply lratCheckerSound f140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p140
  · intro a ha; simp [p140] at ha; subst a; trivial
  · exact checked140
theorem derived140 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c140 := by
  apply localUnsat_implies_entails f140 [c137, c126, c132, c9] c140 unsat140 (by rfl) a
  have h0 : Entails.eval a c137 := derived137 a h
  have h1 : Entails.eval a c126 := derived126 a h
  have h2 : Entails.eval a c132 := derived132 a h
  have h3 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c141 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f141 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c138, some c126, some c140, some c57, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p141 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked141 : lratChecker f141 p141 = .success := by decide +kernel
theorem unsat141 : Unsatisfiable (PosFin 31) f141 := by
  apply lratCheckerSound f141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p141
  · intro a ha; simp [p141] at ha; subst a; trivial
  · exact checked141
theorem derived141 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c141 := by
  apply localUnsat_implies_entails f141 [c138, c126, c140, c57] c141 unsat141 (by rfl) a
  have h0 : Entails.eval a c138 := derived138 a h
  have h1 : Entails.eval a c126 := derived126 a h
  have h2 : Entails.eval a c140 := derived140 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c142 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f142 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c138, some c141, some c139, some c135, some c130, some c131, some c90]
def p142 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked142 : lratChecker f142 p142 = .success := by decide +kernel
theorem unsat142 : Unsatisfiable (PosFin 31) f142 := by
  apply lratCheckerSound f142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p142
  · intro a ha; simp [p142] at ha; subst a; trivial
  · exact checked142
theorem derived142 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c142 := by
  apply localUnsat_implies_entails f142 [c138, c141, c139, c135, c130, c131, c90] c142 unsat142 (by rfl) a
  have h0 : Entails.eval a c138 := derived138 a h
  have h1 : Entails.eval a c141 := derived141 a h
  have h2 : Entails.eval a c139 := derived139 a h
  have h3 : Entails.eval a c135 := derived135 a h
  have h4 : Entails.eval a c130 := derived130 a h
  have h5 : Entails.eval a c131 := derived131 a h
  have h6 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived142

end CochromaticTwenty.Certificates.Z12Direct_5_5_2
