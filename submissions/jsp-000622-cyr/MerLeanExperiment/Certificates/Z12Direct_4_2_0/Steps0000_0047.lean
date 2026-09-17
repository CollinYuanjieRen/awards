import MerLeanExperiment.Certificates.Z12Direct_4_2_0.Inputs

/-! Generated from the actual pinned z12direct_4_2_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c96 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f96 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c88, some c91, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p96 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked96 : lratChecker f96 p96 = .success := by decide +kernel
theorem unsat96 : Unsatisfiable (PosFin 29) f96 := by
  apply lratCheckerSound f96 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p96
  · intro a ha; simp [p96] at ha; subst a; trivial
  · exact checked96
theorem derived96 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c96 := by
  apply localUnsat_implies_entails f96 [c61, c88, c91] c96 unsat96 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c97 : DefaultClause 29 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f97 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c96, some c92, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p97 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked97 : lratChecker f97 p97 = .success := by decide +kernel
theorem unsat97 : Unsatisfiable (PosFin 29) f97 := by
  apply lratCheckerSound f97 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p97
  · intro a ha; simp [p97] at ha; subst a; trivial
  · exact checked97
theorem derived97 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c97 := by
  apply localUnsat_implies_entails f97 [c96, c92] c97 unsat97 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c98 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f98 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c78, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p98 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked98 : lratChecker f98 p98 = .success := by decide +kernel
theorem unsat98 : Unsatisfiable (PosFin 29) f98 := by
  apply lratCheckerSound f98 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p98
  · intro a ha; simp [p98] at ha; subst a; trivial
  · exact checked98
theorem derived98 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c98 := by
  apply localUnsat_implies_entails f98 [c97, c78] c98 unsat98 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c99 : DefaultClause 29 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f99 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c83, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p99 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked99 : lratChecker f99 p99 = .success := by decide +kernel
theorem unsat99 : Unsatisfiable (PosFin 29) f99 := by
  apply lratCheckerSound f99 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p99
  · intro a ha; simp [p99] at ha; subst a; trivial
  · exact checked99
theorem derived99 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c99 := by
  apply localUnsat_implies_entails f99 [c97, c83] c99 unsat99 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c100 : DefaultClause 29 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f100 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c91, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p100 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked100 : lratChecker f100 p100 = .success := by decide +kernel
theorem unsat100 : Unsatisfiable (PosFin 29) f100 := by
  apply lratCheckerSound f100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p100
  · intro a ha; simp [p100] at ha; subst a; trivial
  · exact checked100
theorem derived100 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c100 := by
  apply localUnsat_implies_entails f100 [c98, c91] c100 unsat100 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c101 : DefaultClause 29 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f101 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c100, some c85, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p101 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked101 : lratChecker f101 p101 = .success := by decide +kernel
theorem unsat101 : Unsatisfiable (PosFin 29) f101 := by
  apply lratCheckerSound f101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p101
  · intro a ha; simp [p101] at ha; subst a; trivial
  · exact checked101
theorem derived101 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c101 := by
  apply localUnsat_implies_entails f101 [c100, c85] c101 unsat101 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c102 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f102 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c100, some c97, some c14, some c19, some c38, some c22, some c9, some c70, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p102 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked102 : lratChecker f102 p102 = .success := by decide +kernel
theorem unsat102 : Unsatisfiable (PosFin 29) f102 := by
  apply lratCheckerSound f102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p102
  · intro a ha; simp [p102] at ha; subst a; trivial
  · exact checked102
theorem derived102 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c102 := by
  apply localUnsat_implies_entails f102 [c100, c97, c14, c19, c38, c22, c9, c70] c102 unsat102 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c97 := derived97 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c103 : DefaultClause 29 := directClause [(⟨10, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f103 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c100, some c9, some c10, some c32, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p103 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked103 : lratChecker f103 p103 = .success := by decide +kernel
theorem unsat103 : Unsatisfiable (PosFin 29) f103 := by
  apply lratCheckerSound f103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p103
  · intro a ha; simp [p103] at ha; subst a; trivial
  · exact checked103
theorem derived103 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c103 := by
  apply localUnsat_implies_entails f103 [c97, c100, c9, c10, c32] c103 unsat103 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c100 := derived100 a h
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c104 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f104 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c100, some c97, some c102, some c103, some c19, some c48, some c13, some c4, some c5, some c3, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p104 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked104 : lratChecker f104 p104 = .success := by decide +kernel
theorem unsat104 : Unsatisfiable (PosFin 29) f104 := by
  apply lratCheckerSound f104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p104
  · intro a ha; simp [p104] at ha; subst a; trivial
  · exact checked104
theorem derived104 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c104 := by
  apply localUnsat_implies_entails f104 [c100, c97, c102, c103, c19, c48, c13, c4, c5, c3] c104 unsat104 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c97 := derived97 a h
  have h2 : Entails.eval a c102 := derived102 a h
  have h3 : Entails.eval a c103 := derived103 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c105 : DefaultClause 29 := directClause [(⟨17, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f105 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c100, some c39, some c20, some c13, some c14, some c37, some c47, some c50, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p105 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked105 : lratChecker f105 p105 = .success := by decide +kernel
theorem unsat105 : Unsatisfiable (PosFin 29) f105 := by
  apply lratCheckerSound f105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p105
  · intro a ha; simp [p105] at ha; subst a; trivial
  · exact checked105
theorem derived105 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c105 := by
  apply localUnsat_implies_entails f105 [c97, c100, c39, c20, c13, c14, c37, c47, c50] c105 unsat105 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c100 := derived100 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c106 : DefaultClause 29 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f106 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c100, some c19, some c38, some c9, some c10, some c4, some c5, some c2, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p106 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked106 : lratChecker f106 p106 = .success := by decide +kernel
theorem unsat106 : Unsatisfiable (PosFin 29) f106 := by
  apply lratCheckerSound f106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p106
  · intro a ha; simp [p106] at ha; subst a; trivial
  · exact checked106
theorem derived106 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c106 := by
  apply localUnsat_implies_entails f106 [c97, c100, c19, c38, c9, c10, c4, c5, c2] c106 unsat106 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c100 := derived100 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c107 : DefaultClause 29 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f107 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c100, some c97, some c13, some c14, some c105, some c104, some c21, some c40, some c37, some c47, some c49, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p107 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked107 : lratChecker f107 p107 = .success := by decide +kernel
theorem unsat107 : Unsatisfiable (PosFin 29) f107 := by
  apply lratCheckerSound f107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p107
  · intro a ha; simp [p107] at ha; subst a; trivial
  · exact checked107
theorem derived107 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c107 := by
  apply localUnsat_implies_entails f107 [c100, c97, c13, c14, c105, c104, c21, c40, c37, c47, c49] c107 unsat107 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c97 := derived97 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c105 := derived105 a h
  have h5 : Entails.eval a c104 := derived104 a h
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c108 : DefaultClause 29 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f108 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c106, some c107, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p108 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked108 : lratChecker f108 p108 = .success := by decide +kernel
theorem unsat108 : Unsatisfiable (PosFin 29) f108 := by
  apply lratCheckerSound f108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p108
  · intro a ha; simp [p108] at ha; subst a; trivial
  · exact checked108
theorem derived108 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c108 := by
  apply localUnsat_implies_entails f108 [c106, c107] c108 unsat108 (by rfl) a
  have h0 : Entails.eval a c106 := derived106 a h
  have h1 : Entails.eval a c107 := derived107 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c109 : DefaultClause 29 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f109 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c40, some c21, some c37, some c47, some c49, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p109 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked109 : lratChecker f109 p109 = .success := by decide +kernel
theorem unsat109 : Unsatisfiable (PosFin 29) f109 := by
  apply lratCheckerSound f109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p109
  · intro a ha; simp [p109] at ha; subst a; trivial
  · exact checked109
theorem derived109 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c109 := by
  apply localUnsat_implies_entails f109 [c40, c21, c37, c47, c49] c109 unsat109 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c110 : DefaultClause 29 := directClause [(⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f110 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c108, some c40, some c21, some c18, some c36, some c46, some c55, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p110 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked110 : lratChecker f110 p110 = .success := by decide +kernel
theorem unsat110 : Unsatisfiable (PosFin 29) f110 := by
  apply lratCheckerSound f110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p110
  · intro a ha; simp [p110] at ha; subst a; trivial
  · exact checked110
theorem derived110 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c110 := by
  apply localUnsat_implies_entails f110 [c98, c108, c40, c21, c18, c36, c46, c55] c110 unsat110 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c108 := derived108 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c111 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f111 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c100, some c21, some c40, some c110, some c109, some c43, some c26, some c86, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p111 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked111 : lratChecker f111 p111 = .success := by decide +kernel
theorem unsat111 : Unsatisfiable (PosFin 29) f111 := by
  apply lratCheckerSound f111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p111
  · intro a ha; simp [p111] at ha; subst a; trivial
  · exact checked111
theorem derived111 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c111 := by
  apply localUnsat_implies_entails f111 [c100, c21, c40, c110, c109, c43, c26, c86] c111 unsat111 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c110 := derived110 a h
  have h4 : Entails.eval a c109 := derived109 a h
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c112 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f112 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c16, some c7, some c25, some c33, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p112 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked112 : lratChecker f112 p112 = .success := by decide +kernel
theorem unsat112 : Unsatisfiable (PosFin 29) f112 := by
  apply lratCheckerSound f112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p112
  · intro a ha; simp [p112] at ha; subst a; trivial
  · exact checked112
theorem derived112 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c112 := by
  apply localUnsat_implies_entails f112 [c16, c7, c25, c33] c112 unsat112 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c113 : DefaultClause 29 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f113 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c100, some c98, some c108, some c111, some c16, some c112, some c24, some c22, some c26, some c32, some c80, some c50, some c29, some c56, some c60, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p113 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked113 : lratChecker f113 p113 = .success := by decide +kernel
theorem unsat113 : Unsatisfiable (PosFin 29) f113 := by
  apply lratCheckerSound f113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p113
  · intro a ha; simp [p113] at ha; subst a; trivial
  · exact checked113
theorem derived113 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c113 := by
  apply localUnsat_implies_entails f113 [c100, c98, c108, c111, c16, c112, c24, c22, c26, c32, c80, c50, c29, c56, c60] c113 unsat113 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c98 := derived98 a h
  have h2 : Entails.eval a c108 := derived108 a h
  have h3 : Entails.eval a c111 := derived111 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c112 := derived112 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c29 := h 28 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c114 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f114 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c101, some c100, some c18, some c31, some c28, some c29, some c48, some c90, some c65, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p114 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked114 : lratChecker f114 p114 = .success := by decide +kernel
theorem unsat114 : Unsatisfiable (PosFin 29) f114 := by
  apply lratCheckerSound f114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p114
  · intro a ha; simp [p114] at ha; subst a; trivial
  · exact checked114
theorem derived114 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c114 := by
  apply localUnsat_implies_entails f114 [c98, c101, c100, c18, c31, c28, c29, c48, c90, c65] c114 unsat114 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c101 := derived101 a h
  have h2 : Entails.eval a c100 := derived100 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c115 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f115 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c100, some c96, some c99, some c111, some c16, some c113, some c114, some c26, some c36, some c87, some c62, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p115 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked115 : lratChecker f115 p115 = .success := by decide +kernel
theorem unsat115 : Unsatisfiable (PosFin 29) f115 := by
  apply lratCheckerSound f115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p115
  · intro a ha; simp [p115] at ha; subst a; trivial
  · exact checked115
theorem derived115 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c115 := by
  apply localUnsat_implies_entails f115 [c100, c96, c99, c111, c16, c113, c114, c26, c36, c87, c62] c115 unsat115 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c99 := derived99 a h
  have h3 : Entails.eval a c111 := derived111 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c113 := derived113 a h
  have h6 : Entails.eval a c114 := derived114 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c116 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f116 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c115, some c111, some c32, some c8, some c29, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p116 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked116 : lratChecker f116 p116 = .success := by decide +kernel
theorem unsat116 : Unsatisfiable (PosFin 29) f116 := by
  apply lratCheckerSound f116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p116
  · intro a ha; simp [p116] at ha; subst a; trivial
  · exact checked116
theorem derived116 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c116 := by
  apply localUnsat_implies_entails f116 [c115, c111, c32, c8, c29] c116 unsat116 (by rfl) a
  have h0 : Entails.eval a c115 := derived115 a h
  have h1 : Entails.eval a c111 := derived111 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c117 : DefaultClause 29 := directClause [(⟨18, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f117 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c96, some c108, some c97, some c111, some c18, some c116, some c24, some c36, some c67, some c31, some c50, some c28, some c30, some c76, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p117 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked117 : lratChecker f117 p117 = .success := by decide +kernel
theorem unsat117 : Unsatisfiable (PosFin 29) f117 := by
  apply lratCheckerSound f117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p117
  · intro a ha; simp [p117] at ha; subst a; trivial
  · exact checked117
theorem derived117 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c117 := by
  apply localUnsat_implies_entails f117 [c96, c108, c97, c111, c18, c116, c24, c36, c67, c31, c50, c28, c30, c76] c117 unsat117 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c108 := derived108 a h
  have h2 : Entails.eval a c97 := derived97 a h
  have h3 : Entails.eval a c111 := derived111 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c116 := derived116 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c118 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f118 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c108, some c97, some c75, some c84, some c94, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p118 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked118 : lratChecker f118 p118 = .success := by decide +kernel
theorem unsat118 : Unsatisfiable (PosFin 29) f118 := by
  apply lratCheckerSound f118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p118
  · intro a ha; simp [p118] at ha; subst a; trivial
  · exact checked118
theorem derived118 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c118 := by
  apply localUnsat_implies_entails f118 [c98, c108, c97, c75, c84, c94] c118 unsat118 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c108 := derived108 a h
  have h2 : Entails.eval a c97 := derived97 a h
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c119 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f119 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c96, some c108, some c97, some c47, some c49, some c118, some c74, some c68, some c52, some c82, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p119 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked119 : lratChecker f119 p119 = .success := by decide +kernel
theorem unsat119 : Unsatisfiable (PosFin 29) f119 := by
  apply lratCheckerSound f119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p119
  · intro a ha; simp [p119] at ha; subst a; trivial
  · exact checked119
theorem derived119 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c119 := by
  apply localUnsat_implies_entails f119 [c96, c108, c97, c47, c49, c118, c74, c68, c52, c82] c119 unsat119 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c108 := derived108 a h
  have h2 : Entails.eval a c97 := derived97 a h
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c118 := derived118 a h
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c120 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f120 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c96, some c108, some c59, some c58, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p120 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked120 : lratChecker f120 p120 = .success := by decide +kernel
theorem unsat120 : Unsatisfiable (PosFin 29) f120 := by
  apply lratCheckerSound f120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p120
  · intro a ha; simp [p120] at ha; subst a; trivial
  · exact checked120
theorem derived120 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c120 := by
  apply localUnsat_implies_entails f120 [c98, c96, c108, c59, c58] c120 unsat120 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c108 := derived108 a h
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c121 : DefaultClause 29 := directClause [(⟨17, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f121 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c108, some c96, some c111, some c115, some c117, some c119, some c50, some c37, some c49, some c120, some c24, some c51, some c69, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p121 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked121 : lratChecker f121 p121 = .success := by decide +kernel
theorem unsat121 : Unsatisfiable (PosFin 29) f121 := by
  apply lratCheckerSound f121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p121
  · intro a ha; simp [p121] at ha; subst a; trivial
  · exact checked121
theorem derived121 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c121 := by
  apply localUnsat_implies_entails f121 [c108, c96, c111, c115, c117, c119, c50, c37, c49, c120, c24, c51, c69] c121 unsat121 (by rfl) a
  have h0 : Entails.eval a c108 := derived108 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c111 := derived111 a h
  have h3 : Entails.eval a c115 := derived115 a h
  have h4 : Entails.eval a c117 := derived117 a h
  have h5 : Entails.eval a c119 := derived119 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c120 := derived120 a h
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c122 : DefaultClause 29 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f122 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c96, some c99, some c50, some c37, some c49, some c120, some c51, some c63, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p122 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked122 : lratChecker f122 p122 = .success := by decide +kernel
theorem unsat122 : Unsatisfiable (PosFin 29) f122 := by
  apply lratCheckerSound f122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p122
  · intro a ha; simp [p122] at ha; subst a; trivial
  · exact checked122
theorem derived122 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c122 := by
  apply localUnsat_implies_entails f122 [c96, c99, c50, c37, c49, c120, c51, c63] c122 unsat122 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c99 := derived99 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c120 := derived120 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c123 : DefaultClause 29 := directClause [(⟨7, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f123 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c40, some c122, some c22, some c112, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p123 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked123 : lratChecker f123 p123 = .success := by decide +kernel
theorem unsat123 : Unsatisfiable (PosFin 29) f123 := by
  apply lratCheckerSound f123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p123
  · intro a ha; simp [p123] at ha; subst a; trivial
  · exact checked123
theorem derived123 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c123 := by
  apply localUnsat_implies_entails f123 [c40, c122, c22, c112] c123 unsat123 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c122 := derived122 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c112 := derived112 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c124 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f124 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c100, some c98, some c108, some c97, some c19, some c123, some c38, some c86, some c112, some c75, some c42, some c6, some c66, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p124 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked124 : lratChecker f124 p124 = .success := by decide +kernel
theorem unsat124 : Unsatisfiable (PosFin 29) f124 := by
  apply lratCheckerSound f124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p124
  · intro a ha; simp [p124] at ha; subst a; trivial
  · exact checked124
theorem derived124 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c124 := by
  apply localUnsat_implies_entails f124 [c100, c98, c108, c97, c19, c123, c38, c86, c112, c75, c42, c6, c66] c124 unsat124 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c98 := derived98 a h
  have h2 : Entails.eval a c108 := derived108 a h
  have h3 : Entails.eval a c97 := derived97 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c123 := derived123 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c112 := derived112 a h
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c125 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f125 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c96, some c99, some c97, some c19, some c124, some c22, some c23, some c11, some c93, some c64, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p125 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked125 : lratChecker f125 p125 = .success := by decide +kernel
theorem unsat125 : Unsatisfiable (PosFin 29) f125 := by
  apply lratCheckerSound f125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p125
  · intro a ha; simp [p125] at ha; subst a; trivial
  · exact checked125
theorem derived125 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c125 := by
  apply localUnsat_implies_entails f125 [c96, c99, c97, c19, c124, c22, c23, c11, c93, c64] c125 unsat125 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c99 := derived99 a h
  have h2 : Entails.eval a c97 := derived97 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c124 := derived124 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c126 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f126 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c96, some c99, some c121, some c125, some c109, some c19, some c71, some c93, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p126 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked126 : lratChecker f126 p126 = .success := by decide +kernel
theorem unsat126 : Unsatisfiable (PosFin 29) f126 := by
  apply lratCheckerSound f126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p126
  · intro a ha; simp [p126] at ha; subst a; trivial
  · exact checked126
theorem derived126 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c126 := by
  apply localUnsat_implies_entails f126 [c97, c96, c99, c121, c125, c109, c19, c71, c93] c126 unsat126 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c99 := derived99 a h
  have h3 : Entails.eval a c121 := derived121 a h
  have h4 : Entails.eval a c125 := derived125 a h
  have h5 : Entails.eval a c109 := derived109 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c127 : DefaultClause 29 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f127 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c108, some c97, some c121, some c38, some c19, some c123, some c125, some c109, some c126, some c79, some c75, some c72, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p127 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked127 : lratChecker f127 p127 = .success := by decide +kernel
theorem unsat127 : Unsatisfiable (PosFin 29) f127 := by
  apply lratCheckerSound f127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p127
  · intro a ha; simp [p127] at ha; subst a; trivial
  · exact checked127
theorem derived127 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c127 := by
  apply localUnsat_implies_entails f127 [c98, c108, c97, c121, c38, c19, c123, c125, c109, c126, c79, c75, c72] c127 unsat127 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c108 := derived108 a h
  have h2 : Entails.eval a c97 := derived97 a h
  have h3 : Entails.eval a c121 := derived121 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c123 := derived123 a h
  have h7 : Entails.eval a c125 := derived125 a h
  have h8 : Entails.eval a c109 := derived109 a h
  have h9 : Entails.eval a c126 := derived126 a h
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c128 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f128 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c121, some c19, some c38, some c127, some c18, some c28, some c44, some c1, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p128 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked128 : lratChecker f128 p128 = .success := by decide +kernel
theorem unsat128 : Unsatisfiable (PosFin 29) f128 := by
  apply lratCheckerSound f128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p128
  · intro a ha; simp [p128] at ha; subst a; trivial
  · exact checked128
theorem derived128 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c128 := by
  apply localUnsat_implies_entails f128 [c121, c19, c38, c127, c18, c28, c44, c1] c128 unsat128 (by rfl) a
  have h0 : Entails.eval a c121 := derived121 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c127 := derived127 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c129 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f129 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c128, some c20, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p129 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked129 : lratChecker f129 p129 = .success := by decide +kernel
theorem unsat129 : Unsatisfiable (PosFin 29) f129 := by
  apply lratCheckerSound f129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p129
  · intro a ha; simp [p129] at ha; subst a; trivial
  · exact checked129
theorem derived129 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c129 := by
  apply localUnsat_implies_entails f129 [c128, c20] c129 unsat129 (by rfl) a
  have h0 : Entails.eval a c128 := derived128 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c130 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f130 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c128, some c39, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p130 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked130 : lratChecker f130 p130 = .success := by decide +kernel
theorem unsat130 : Unsatisfiable (PosFin 29) f130 := by
  apply lratCheckerSound f130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p130
  · intro a ha; simp [p130] at ha; subst a; trivial
  · exact checked130
theorem derived130 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c130 := by
  apply localUnsat_implies_entails f130 [c128, c39] c130 unsat130 (by rfl) a
  have h0 : Entails.eval a c128 := derived128 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c131 : DefaultClause 29 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨8, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f131 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c96, some c99, some c97, some c129, some c128, some c38, some c89, some c41, some c81, some c73, some c34, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p131 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked131 : lratChecker f131 p131 = .success := by decide +kernel
theorem unsat131 : Unsatisfiable (PosFin 29) f131 := by
  apply lratCheckerSound f131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p131
  · intro a ha; simp [p131] at ha; subst a; trivial
  · exact checked131
theorem derived131 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c131 := by
  apply localUnsat_implies_entails f131 [c96, c99, c97, c129, c128, c38, c89, c41, c81, c73, c34] c131 unsat131 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c99 := derived99 a h
  have h2 : Entails.eval a c97 := derived97 a h
  have h3 : Entails.eval a c129 := derived129 a h
  have h4 : Entails.eval a c128 := derived128 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c132 : DefaultClause 29 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f132 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c130, some c129, some c17, some c30, some c45, some c1, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p132 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked132 : lratChecker f132 p132 = .success := by decide +kernel
theorem unsat132 : Unsatisfiable (PosFin 29) f132 := by
  apply lratCheckerSound f132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p132
  · intro a ha; simp [p132] at ha; subst a; trivial
  · exact checked132
theorem derived132 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c132 := by
  apply localUnsat_implies_entails f132 [c130, c129, c17, c30, c45, c1] c132 unsat132 (by rfl) a
  have h0 : Entails.eval a c130 := derived130 a h
  have h1 : Entails.eval a c129 := derived129 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c133 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f133 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c96, some c99, some c128, some c97, some c129, some c132, some c38, some c89, some c131, some c73, some c21, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p133 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked133 : lratChecker f133 p133 = .success := by decide +kernel
theorem unsat133 : Unsatisfiable (PosFin 29) f133 := by
  apply lratCheckerSound f133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p133
  · intro a ha; simp [p133] at ha; subst a; trivial
  · exact checked133
theorem derived133 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c133 := by
  apply localUnsat_implies_entails f133 [c96, c99, c128, c97, c129, c132, c38, c89, c131, c73, c21] c133 unsat133 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c99 := derived99 a h
  have h2 : Entails.eval a c128 := derived128 a h
  have h3 : Entails.eval a c97 := derived97 a h
  have h4 : Entails.eval a c129 := derived129 a h
  have h5 : Entails.eval a c132 := derived132 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c131 := derived131 a h
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c134 : DefaultClause 29 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f134 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c130, some c100, some c129, some c132, some c19, some c38, some c133, some c77, some c12, some c95, some c50, some c120, some c57, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p134 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked134 : lratChecker f134 p134 = .success := by decide +kernel
theorem unsat134 : Unsatisfiable (PosFin 29) f134 := by
  apply lratCheckerSound f134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p134
  · intro a ha; simp [p134] at ha; subst a; trivial
  · exact checked134
theorem derived134 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c134 := by
  apply localUnsat_implies_entails f134 [c97, c130, c100, c129, c132, c19, c38, c133, c77, c12, c95, c50, c120, c57] c134 unsat134 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c130 := derived130 a h
  have h2 : Entails.eval a c100 := derived100 a h
  have h3 : Entails.eval a c129 := derived129 a h
  have h4 : Entails.eval a c132 := derived132 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c133 := derived133 a h
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c120 := derived120 a h
  have h13 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c135 : DefaultClause 29 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f135 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c134, some c130, some c19, some c125, some c123, some c47, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p135 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked135 : lratChecker f135 p135 = .success := by decide +kernel
theorem unsat135 : Unsatisfiable (PosFin 29) f135 := by
  apply lratCheckerSound f135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p135
  · intro a ha; simp [p135] at ha; subst a; trivial
  · exact checked135
theorem derived135 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c135 := by
  apply localUnsat_implies_entails f135 [c134, c130, c19, c125, c123, c47] c135 unsat135 (by rfl) a
  have h0 : Entails.eval a c134 := derived134 a h
  have h1 : Entails.eval a c130 := derived130 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c125 := derived125 a h
  have h4 : Entails.eval a c123 := derived123 a h
  have h5 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c136 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f136 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c135, some c128, some c27, some c26, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p136 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked136 : lratChecker f136 p136 = .success := by decide +kernel
theorem unsat136 : Unsatisfiable (PosFin 29) f136 := by
  apply lratCheckerSound f136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p136
  · intro a ha; simp [p136] at ha; subst a; trivial
  · exact checked136
theorem derived136 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c136 := by
  apply localUnsat_implies_entails f136 [c135, c128, c27, c26] c136 unsat136 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c128 := derived128 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c137 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f137 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c135, some c134, some c130, some c129, some c136, some c50, some c119, some c53, some c54, some c21, some c33, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p137 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked137 : lratChecker f137 p137 = .success := by decide +kernel
theorem unsat137 : Unsatisfiable (PosFin 29) f137 := by
  apply lratCheckerSound f137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p137
  · intro a ha; simp [p137] at ha; subst a; trivial
  · exact checked137
theorem derived137 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c137 := by
  apply localUnsat_implies_entails f137 [c135, c134, c130, c129, c136, c50, c119, c53, c54, c21, c33] c137 unsat137 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c134 := derived134 a h
  have h2 : Entails.eval a c130 := derived130 a h
  have h3 : Entails.eval a c129 := derived129 a h
  have h4 : Entails.eval a c136 := derived136 a h
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c119 := derived119 a h
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c138 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f138 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c137, some c135, some c134, some c21, some c50, some c112, some c119, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p138 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked138 : lratChecker f138 p138 = .success := by decide +kernel
theorem unsat138 : Unsatisfiable (PosFin 29) f138 := by
  apply lratCheckerSound f138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p138
  · intro a ha; simp [p138] at ha; subst a; trivial
  · exact checked138
theorem derived138 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c138 := by
  apply localUnsat_implies_entails f138 [c137, c135, c134, c21, c50, c112, c119] c138 unsat138 (by rfl) a
  have h0 : Entails.eval a c137 := derived137 a h
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c134 := derived134 a h
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c112 := derived112 a h
  have h6 : Entails.eval a c119 := derived119 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c139 : DefaultClause 29 := directClause [(⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f139 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c138, some c134, some c129, some c37, some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p139 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked139 : lratChecker f139 p139 = .success := by decide +kernel
theorem unsat139 : Unsatisfiable (PosFin 29) f139 := by
  apply lratCheckerSound f139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p139
  · intro a ha; simp [p139] at ha; subst a; trivial
  · exact checked139
theorem derived139 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c139 := by
  apply localUnsat_implies_entails f139 [c138, c134, c129, c37] c139 unsat139 (by rfl) a
  have h0 : Entails.eval a c138 := derived138 a h
  have h1 : Entails.eval a c134 := derived134 a h
  have h2 : Entails.eval a c129 := derived129 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c140 : DefaultClause 29 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f140 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c135, some c15, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p140 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked140 : lratChecker f140 p140 = .success := by decide +kernel
theorem unsat140 : Unsatisfiable (PosFin 29) f140 := by
  apply lratCheckerSound f140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p140
  · intro a ha; simp [p140] at ha; subst a; trivial
  · exact checked140
theorem derived140 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c140 := by
  apply localUnsat_implies_entails f140 [c139, c135, c15] c140 unsat140 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c141 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f141 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c140, some c138, some c128, some c35, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p141 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked141 : lratChecker f141 p141 = .success := by decide +kernel
theorem unsat141 : Unsatisfiable (PosFin 29) f141 := by
  apply lratCheckerSound f141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p141
  · intro a ha; simp [p141] at ha; subst a; trivial
  · exact checked141
theorem derived141 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c141 := by
  apply localUnsat_implies_entails f141 [c140, c138, c128, c35] c141 unsat141 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c138 := derived138 a h
  have h2 : Entails.eval a c128 := derived128 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c142 : DefaultClause 29 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f142 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c140, some c100, some c137, some c87, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p142 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked142 : lratChecker f142 p142 = .success := by decide +kernel
theorem unsat142 : Unsatisfiable (PosFin 29) f142 := by
  apply lratCheckerSound f142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p142
  · intro a ha; simp [p142] at ha; subst a; trivial
  · exact checked142
theorem derived142 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c142 := by
  apply localUnsat_implies_entails f142 [c140, c100, c137, c87] c142 unsat142 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c100 := derived100 a h
  have h2 : Entails.eval a c137 := derived137 a h
  have h3 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c143 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f143 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c142, some c140, some c141, some c134, some c108, some c98, some c80]
def p143 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked143 : lratChecker f143 p143 = .success := by decide +kernel
theorem unsat143 : Unsatisfiable (PosFin 29) f143 := by
  apply lratCheckerSound f143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p143
  · intro a ha; simp [p143] at ha; subst a; trivial
  · exact checked143
theorem derived143 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c143 := by
  apply localUnsat_implies_entails f143 [c142, c140, c141, c134, c108, c98, c80] c143 unsat143 (by rfl) a
  have h0 : Entails.eval a c142 := derived142 a h
  have h1 : Entails.eval a c140 := derived140 a h
  have h2 : Entails.eval a c141 := derived141 a h
  have h3 : Entails.eval a c134 := derived134 a h
  have h4 : Entails.eval a c108 := derived108 a h
  have h5 : Entails.eval a c98 := derived98 a h
  have h6 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived143

end CochromaticTwenty.Certificates.Z12Direct_4_2_0
