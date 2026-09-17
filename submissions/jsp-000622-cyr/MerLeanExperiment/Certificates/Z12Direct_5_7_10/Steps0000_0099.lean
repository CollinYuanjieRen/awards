import MerLeanExperiment.Certificates.Z12Direct_5_7_10.Inputs

/-! Generated from the actual pinned z12direct_5_7_10-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_10
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c173 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f173 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c45, some c43, some c29, some c31, some c23, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p173 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked173 : lratChecker f173 p173 = .success := by decide +kernel
theorem unsat173 : Unsatisfiable (PosFin 31) f173 := by
  apply lratCheckerSound f173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p173
  · intro a ha; simp [p173] at ha; subst a; trivial
  · exact checked173
theorem derived173 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c173 := by
  apply localUnsat_implies_entails f173 [c45, c43, c29, c31, c23] c173 unsat173 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c174 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f174 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c43, some c45, some c173, some c146, some c28, some c30, some c23, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p174 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked174 : lratChecker f174 p174 = .success := by decide +kernel
theorem unsat174 : Unsatisfiable (PosFin 31) f174 := by
  apply lratCheckerSound f174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p174
  · intro a ha; simp [p174] at ha; subst a; trivial
  · exact checked174
theorem derived174 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c174 := by
  apply localUnsat_implies_entails f174 [c43, c45, c173, c146, c28, c30, c23] c174 unsat174 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c173 := derived173 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c175 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f175 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c28, some c30, some c23, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p175 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked175 : lratChecker f175 p175 = .success := by decide +kernel
theorem unsat175 : Unsatisfiable (PosFin 31) f175 := by
  apply lratCheckerSound f175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p175
  · intro a ha; simp [p175] at ha; subst a; trivial
  · exact checked175
theorem derived175 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c175 := by
  apply localUnsat_implies_entails f175 [c28, c30, c23] c175 unsat175 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c176 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f176 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c175, some c146, some c29, some c31, some c23, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p176 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked176 : lratChecker f176 p176 = .success := by decide +kernel
theorem unsat176 : Unsatisfiable (PosFin 31) f176 := by
  apply lratCheckerSound f176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p176
  · intro a ha; simp [p176] at ha; subst a; trivial
  · exact checked176
theorem derived176 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c176 := by
  apply localUnsat_implies_entails f176 [c175, c146, c29, c31, c23] c176 unsat176 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c177 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f177 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c29, some c31, some c143, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p177 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked177 : lratChecker f177 p177 = .success := by decide +kernel
theorem unsat177 : Unsatisfiable (PosFin 31) f177 := by
  apply lratCheckerSound f177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p177
  · intro a ha; simp [p177] at ha; subst a; trivial
  · exact checked177
theorem derived177 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c177 := by
  apply localUnsat_implies_entails f177 [c29, c31, c143] c177 unsat177 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c178 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f178 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c174, some c60, some c56, some c42, some c177, some c8, some c85, some c89, some c13, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p178 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked178 : lratChecker f178 p178 = .success := by decide +kernel
theorem unsat178 : Unsatisfiable (PosFin 31) f178 := by
  apply lratCheckerSound f178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p178
  · intro a ha; simp [p178] at ha; subst a; trivial
  · exact checked178
theorem derived178 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c178 := by
  apply localUnsat_implies_entails f178 [c174, c60, c56, c42, c177, c8, c85, c89, c13] c178 unsat178 (by rfl) a
  have h0 : Entails.eval a c174 := derived174 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c177 := derived177 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c179 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f179 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c60, some c56, some c174, some c178, some c176, some c44, some c177, some c8, some c86, some c90, some c13, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p179 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked179 : lratChecker f179 p179 = .success := by decide +kernel
theorem unsat179 : Unsatisfiable (PosFin 31) f179 := by
  apply lratCheckerSound f179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p179
  · intro a ha; simp [p179] at ha; subst a; trivial
  · exact checked179
theorem derived179 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c179 := by
  apply localUnsat_implies_entails f179 [c60, c56, c174, c178, c176, c44, c177, c8, c86, c90, c13] c179 unsat179 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c174 := derived174 a h
  have h3 : Entails.eval a c178 := derived178 a h
  have h4 : Entails.eval a c176 := derived176 a h
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c177 := derived177 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c180 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f180 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c24, some c30, some c143, some c32, some c36, some c154, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p180 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked180 : lratChecker f180 p180 = .success := by decide +kernel
theorem unsat180 : Unsatisfiable (PosFin 31) f180 := by
  apply lratCheckerSound f180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p180
  · intro a ha; simp [p180] at ha; subst a; trivial
  · exact checked180
theorem derived180 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c180 := by
  apply localUnsat_implies_entails f180 [c24, c30, c143, c32, c36, c154] c180 unsat180 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c143 := h 142 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c181 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f181 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c60, some c56, some c8, some c180, some c44, some c146, some c30, some c7, some c23, some c127, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p181 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked181 : lratChecker f181 p181 = .success := by decide +kernel
theorem unsat181 : Unsatisfiable (PosFin 31) f181 := by
  apply lratCheckerSound f181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p181
  · intro a ha; simp [p181] at ha; subst a; trivial
  · exact checked181
theorem derived181 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c181 := by
  apply localUnsat_implies_entails f181 [c60, c56, c8, c180, c44, c146, c30, c7, c23, c127] c181 unsat181 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c180 := derived180 a h
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c182 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f182 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c181, some c45, some c146, some c30, some c7, some c23, some c83, some c104, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p182 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked182 : lratChecker f182 p182 = .success := by decide +kernel
theorem unsat182 : Unsatisfiable (PosFin 31) f182 := by
  apply lratCheckerSound f182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p182
  · intro a ha; simp [p182] at ha; subst a; trivial
  · exact checked182
theorem derived182 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c182 := by
  apply localUnsat_implies_entails f182 [c56, c181, c45, c146, c30, c7, c23, c83, c104] c182 unsat182 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c181 := derived181 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c183 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f183 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c31, some c45, some c7, some c23, some c83, some c105, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p183 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked183 : lratChecker f183 p183 = .success := by decide +kernel
theorem unsat183 : Unsatisfiable (PosFin 31) f183 := by
  apply lratCheckerSound f183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p183
  · intro a ha; simp [p183] at ha; subst a; trivial
  · exact checked183
theorem derived183 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c183 := by
  apply localUnsat_implies_entails f183 [c31, c45, c7, c23, c83, c105] c183 unsat183 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c184 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f184 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c37, some c154, some c163, some c44, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p184 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked184 : lratChecker f184 p184 = .success := by decide +kernel
theorem unsat184 : Unsatisfiable (PosFin 31) f184 := by
  apply lratCheckerSound f184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p184
  · intro a ha; simp [p184] at ha; subst a; trivial
  · exact checked184
theorem derived184 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c184 := by
  apply localUnsat_implies_entails f184 [c33, c37, c154, c163, c44] c184 unsat184 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c185 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f185 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c182, some c31, some c183, some c184, some c23, some c143, some c44, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p185 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked185 : lratChecker f185 p185 = .success := by decide +kernel
theorem unsat185 : Unsatisfiable (PosFin 31) f185 := by
  apply lratCheckerSound f185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p185
  · intro a ha; simp [p185] at ha; subst a; trivial
  · exact checked185
theorem derived185 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c185 := by
  apply localUnsat_implies_entails f185 [c56, c182, c31, c183, c184, c23, c143, c44] c185 unsat185 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c182 := derived182 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c183 := derived183 a h
  have h4 : Entails.eval a c184 := derived184 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c186 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f186 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c143, some c46, some c50, some c164, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p186 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked186 : lratChecker f186 p186 = .success := by decide +kernel
theorem unsat186 : Unsatisfiable (PosFin 31) f186 := by
  apply lratCheckerSound f186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p186
  · intro a ha; simp [p186] at ha; subst a; trivial
  · exact checked186
theorem derived186 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c186 := by
  apply localUnsat_implies_entails f186 [c143, c46, c50, c164] c186 unsat186 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c187 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨18, by decide⟩, false), (⟨21, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f187 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c60, some c56, some c186, some c33, some c37, some c105, some c154, some c80, some c82, some c44, some c1, some c169, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p187 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked187 : lratChecker f187 p187 = .success := by decide +kernel
theorem unsat187 : Unsatisfiable (PosFin 31) f187 := by
  apply lratCheckerSound f187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p187
  · intro a ha; simp [p187] at ha; subst a; trivial
  · exact checked187
theorem derived187 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c187 := by
  apply localUnsat_implies_entails f187 [c60, c56, c186, c33, c37, c105, c154, c80, c82, c44, c1, c169] c187 unsat187 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c186 := derived186 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c188 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f188 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c185, some c179, some c56, some c31, some c187, some c45, some c67, some c7, some c83, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p188 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked188 : lratChecker f188 p188 = .success := by decide +kernel
theorem unsat188 : Unsatisfiable (PosFin 31) f188 := by
  apply lratCheckerSound f188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p188
  · intro a ha; simp [p188] at ha; subst a; trivial
  · exact checked188
theorem derived188 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c188 := by
  apply localUnsat_implies_entails f188 [c185, c179, c56, c31, c187, c45, c67, c7, c83] c188 unsat188 (by rfl) a
  have h0 : Entails.eval a c185 := derived185 a h
  have h1 : Entails.eval a c179 := derived179 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c187 := derived187 a h
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c189 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f189 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c188, some c185, some c56, some c45, some c47, some c51, some c67, some c158, some c83, some c30, some c7, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p189 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked189 : lratChecker f189 p189 = .success := by decide +kernel
theorem unsat189 : Unsatisfiable (PosFin 31) f189 := by
  apply lratCheckerSound f189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p189
  · intro a ha; simp [p189] at ha; subst a; trivial
  · exact checked189
theorem derived189 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c189 := by
  apply localUnsat_implies_entails f189 [c188, c185, c56, c45, c47, c51, c67, c158, c83, c30, c7] c189 unsat189 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c185 := derived185 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c190 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f190 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c60, some c185, some c188, some c189, some c8, some c180, some c95, some c44, some c66, some c7, some c119, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p190 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked190 : lratChecker f190 p190 = .success := by decide +kernel
theorem unsat190 : Unsatisfiable (PosFin 31) f190 := by
  apply lratCheckerSound f190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p190
  · intro a ha; simp [p190] at ha; subst a; trivial
  · exact checked190
theorem derived190 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c190 := by
  apply localUnsat_implies_entails f190 [c56, c60, c185, c188, c189, c8, c180, c95, c44, c66, c7, c119] c190 unsat190 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c185 := derived185 a h
  have h3 : Entails.eval a c188 := derived188 a h
  have h4 : Entails.eval a c189 := derived189 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c180 := derived180 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c191 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f191 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c126, some c17, some c5, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p191 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked191 : lratChecker f191 p191 = .success := by decide +kernel
theorem unsat191 : Unsatisfiable (PosFin 31) f191 := by
  apply lratCheckerSound f191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p191
  · intro a ha; simp [p191] at ha; subst a; trivial
  · exact checked191
theorem derived191 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c191 := by
  apply localUnsat_implies_entails f191 [c94, c126, c17, c5] c191 unsat191 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c126 := h 125 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c192 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f192 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c125, some c16, some c93, some c5, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p192 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked192 : lratChecker f192 p192 = .success := by decide +kernel
theorem unsat192 : Unsatisfiable (PosFin 31) f192 := by
  apply lratCheckerSound f192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p192
  · intro a ha; simp [p192] at ha; subst a; trivial
  · exact checked192
theorem derived192 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c192 := by
  apply localUnsat_implies_entails f192 [c125, c16, c93, c5] c192 unsat192 (by rfl) a
  have h0 : Entails.eval a c125 := h 124 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c193 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f193 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c191, some c14, some c192, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p193 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked193 : lratChecker f193 p193 = .success := by decide +kernel
theorem unsat193 : Unsatisfiable (PosFin 31) f193 := by
  apply lratCheckerSound f193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p193
  · intro a ha; simp [p193] at ha; subst a; trivial
  · exact checked193
theorem derived193 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c193 := by
  apply localUnsat_implies_entails f193 [c55, c191, c14, c192] c193 unsat193 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c191 := derived191 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c192 := derived192 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c194 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨16, by decide⟩, false), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f194 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c106, some c24, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p194 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked194 : lratChecker f194 p194 = .success := by decide +kernel
theorem unsat194 : Unsatisfiable (PosFin 31) f194 := by
  apply lratCheckerSound f194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p194
  · intro a ha; simp [p194] at ha; subst a; trivial
  · exact checked194
theorem derived194 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c194 := by
  apply localUnsat_implies_entails f194 [c66, c106, c24] c194 unsat194 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c195 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f195 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c85, some c16, some c17, some c14, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p195 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked195 : lratChecker f195 p195 = .success := by decide +kernel
theorem unsat195 : Unsatisfiable (PosFin 31) f195 := by
  apply lratCheckerSound f195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p195
  · intro a ha; simp [p195] at ha; subst a; trivial
  · exact checked195
theorem derived195 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c195 := by
  apply localUnsat_implies_entails f195 [c85, c16, c17, c14] c195 unsat195 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c196 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f196 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c8, some c195, some c66, some c194, some c24, some c143, some c104, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p196 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked196 : lratChecker f196 p196 = .success := by decide +kernel
theorem unsat196 : Unsatisfiable (PosFin 31) f196 := by
  apply lratCheckerSound f196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p196
  · intro a ha; simp [p196] at ha; subst a; trivial
  · exact checked196
theorem derived196 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c196 := by
  apply localUnsat_implies_entails f196 [c8, c195, c66, c194, c24, c143, c104] c196 unsat196 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c195 := derived195 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c194 := derived194 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c143 := h 142 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c197 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f197 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c24, some c143, some c104, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p197 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked197 : lratChecker f197 p197 = .success := by decide +kernel
theorem unsat197 : Unsatisfiable (PosFin 31) f197 := by
  apply lratCheckerSound f197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p197
  · intro a ha; simp [p197] at ha; subst a; trivial
  · exact checked197
theorem derived197 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c197 := by
  apply localUnsat_implies_entails f197 [c24, c143, c104] c197 unsat197 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c198 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f198 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c197, some c68, some c146, some c23, some c104, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p198 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked198 : lratChecker f198 p198 = .success := by decide +kernel
theorem unsat198 : Unsatisfiable (PosFin 31) f198 := by
  apply lratCheckerSound f198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p198
  · intro a ha; simp [p198] at ha; subst a; trivial
  · exact checked198
theorem derived198 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c198 := by
  apply localUnsat_implies_entails f198 [c197, c68, c146, c23, c104] c198 unsat198 (by rfl) a
  have h0 : Entails.eval a c197 := derived197 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c199 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f199 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c198, some c106, some c146, some c24, some c68, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p199 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked199 : lratChecker f199 p199 = .success := by decide +kernel
theorem unsat199 : Unsatisfiable (PosFin 31) f199 := by
  apply lratCheckerSound f199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p199
  · intro a ha; simp [p199] at ha; subst a; trivial
  · exact checked199
theorem derived199 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c199 := by
  apply localUnsat_implies_entails f199 [c198, c106, c146, c24, c68] c199 unsat199 (by rfl) a
  have h0 : Entails.eval a c198 := derived198 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c200 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f200 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c8, some c193, some c196, some c199, some c16, some c17, some c14, some c6, some c118, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p200 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked200 : lratChecker f200 p200 = .success := by decide +kernel
theorem unsat200 : Unsatisfiable (PosFin 31) f200 := by
  apply lratCheckerSound f200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p200
  · intro a ha; simp [p200] at ha; subst a; trivial
  · exact checked200
theorem derived200 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c200 := by
  apply localUnsat_implies_entails f200 [c8, c193, c196, c199, c16, c17, c14, c6, c118] c200 unsat200 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c193 := derived193 a h
  have h2 : Entails.eval a c196 := derived196 a h
  have h3 : Entails.eval a c199 := derived199 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c201 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f201 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c83, some c195, some c14, some c6, some c118, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p201 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked201 : lratChecker f201 p201 = .success := by decide +kernel
theorem unsat201 : Unsatisfiable (PosFin 31) f201 := by
  apply lratCheckerSound f201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p201
  · intro a ha; simp [p201] at ha; subst a; trivial
  · exact checked201
theorem derived201 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c201 := by
  apply localUnsat_implies_entails f201 [c81, c83, c195, c14, c6, c118] c201 unsat201 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c195 := derived195 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c202 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f202 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c67, some c69, some c146, some c104, some c106, some c23, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p202 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked202 : lratChecker f202 p202 = .success := by decide +kernel
theorem unsat202 : Unsatisfiable (PosFin 31) f202 := by
  apply lratCheckerSound f202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p202
  · intro a ha; simp [p202] at ha; subst a; trivial
  · exact checked202
theorem derived202 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c202 := by
  apply localUnsat_implies_entails f202 [c67, c69, c146, c104, c106, c23] c202 unsat202 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c203 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f203 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c190, some c200, some c202, some c81, some c83, some c201, some c14, some c2, some c102, some c148, some c149, some c160, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p203 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked203 : lratChecker f203 p203 = .success := by decide +kernel
theorem unsat203 : Unsatisfiable (PosFin 31) f203 := by
  apply lratCheckerSound f203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p203
  · intro a ha; simp [p203] at ha; subst a; trivial
  · exact checked203
theorem derived203 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c203 := by
  apply localUnsat_implies_entails f203 [c190, c200, c202, c81, c83, c201, c14, c2, c102, c148, c149, c160] c203 unsat203 (by rfl) a
  have h0 : Entails.eval a c190 := derived190 a h
  have h1 : Entails.eval a c200 := derived200 a h
  have h2 : Entails.eval a c202 := derived202 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c201 := derived201 a h
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c204 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨27, by decide⟩, true), (⟨24, by decide⟩, false), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f204 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c83, some c14, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p204 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked204 : lratChecker f204 p204 = .success := by decide +kernel
theorem unsat204 : Unsatisfiable (PosFin 31) f204 := by
  apply lratCheckerSound f204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p204
  · intro a ha; simp [p204] at ha; subst a; trivial
  · exact checked204
theorem derived204 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c204 := by
  apply localUnsat_implies_entails f204 [c81, c83, c14] c204 unsat204 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c205 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f205 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c190, some c200, some c203, some c55, some c193, some c41, some c204, some c5, some c26, some c11, some c158, some c124, some c72, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p205 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked205 : lratChecker f205 p205 = .success := by decide +kernel
theorem unsat205 : Unsatisfiable (PosFin 31) f205 := by
  apply lratCheckerSound f205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p205
  · intro a ha; simp [p205] at ha; subst a; trivial
  · exact checked205
theorem derived205 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c205 := by
  apply localUnsat_implies_entails f205 [c190, c200, c203, c55, c193, c41, c204, c5, c26, c11, c158, c124, c72] c205 unsat205 (by rfl) a
  have h0 : Entails.eval a c190 := derived190 a h
  have h1 : Entails.eval a c200 := derived200 a h
  have h2 : Entails.eval a c203 := derived203 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c193 := derived193 a h
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c204 := derived204 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c206 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f206 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c27, some c41, some c5, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p206 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked206 : lratChecker f206 p206 = .success := by decide +kernel
theorem unsat206 : Unsatisfiable (PosFin 31) f206 := by
  apply lratCheckerSound f206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p206
  · intro a ha; simp [p206] at ha; subst a; trivial
  · exact checked206
theorem derived206 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c206 := by
  apply localUnsat_implies_entails f206 [c27, c41, c5] c206 unsat206 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c207 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f207 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c206, some c107, some c67, some c69, some c105, some c23, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p207 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked207 : lratChecker f207 p207 = .success := by decide +kernel
theorem unsat207 : Unsatisfiable (PosFin 31) f207 := by
  apply lratCheckerSound f207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p207
  · intro a ha; simp [p207] at ha; subst a; trivial
  · exact checked207
theorem derived207 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c207 := by
  apply localUnsat_implies_entails f207 [c206, c107, c67, c69, c105, c23] c207 unsat207 (by rfl) a
  have h0 : Entails.eval a c206 := derived206 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c208 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f208 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c205, some c190, some c207, some c83, some c74, some c75, some c112, some c113, some c22, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p208 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked208 : lratChecker f208 p208 = .success := by decide +kernel
theorem unsat208 : Unsatisfiable (PosFin 31) f208 := by
  apply lratCheckerSound f208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p208
  · intro a ha; simp [p208] at ha; subst a; trivial
  · exact checked208
theorem derived208 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c208 := by
  apply localUnsat_implies_entails f208 [c205, c190, c207, c83, c74, c75, c112, c113, c22] c208 unsat208 (by rfl) a
  have h0 : Entails.eval a c205 := derived205 a h
  have h1 : Entails.eval a c190 := derived190 a h
  have h2 : Entails.eval a c207 := derived207 a h
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c209 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f209 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c205, some c190, some c115, some c116, some c2, some c14, some c54, some c58, some c148, some c149, some c160, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p209 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked209 : lratChecker f209 p209 = .success := by decide +kernel
theorem unsat209 : Unsatisfiable (PosFin 31) f209 := by
  apply lratCheckerSound f209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p209
  · intro a ha; simp [p209] at ha; subst a; trivial
  · exact checked209
theorem derived209 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c209 := by
  apply localUnsat_implies_entails f209 [c205, c190, c115, c116, c2, c14, c54, c58, c148, c149, c160] c209 unsat209 (by rfl) a
  have h0 : Entails.eval a c205 := derived205 a h
  have h1 : Entails.eval a c190 := derived190 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c149 := h 148 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c210 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f210 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c112, some c113, some c5, some c154, some c73, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p210 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked210 : lratChecker f210 p210 = .success := by decide +kernel
theorem unsat210 : Unsatisfiable (PosFin 31) f210 := by
  apply lratCheckerSound f210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p210
  · intro a ha; simp [p210] at ha; subst a; trivial
  · exact checked210
theorem derived210 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c210 := by
  apply localUnsat_implies_entails f210 [c112, c113, c5, c154, c73] c210 unsat210 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c211 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨19, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f211 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c97, some c9, some c79, some c157, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p211 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked211 : lratChecker f211 p211 = .success := by decide +kernel
theorem unsat211 : Unsatisfiable (PosFin 31) f211 := by
  apply lratCheckerSound f211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p211
  · intro a ha; simp [p211] at ha; subst a; trivial
  · exact checked211
theorem derived211 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c211 := by
  apply localUnsat_implies_entails f211 [c97, c9, c79, c157] c211 unsat211 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c212 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f212 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c208, some c205, some c33, some c27, some c35, some c143, some c186, some c23, some c68, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p212 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked212 : lratChecker f212 p212 = .success := by decide +kernel
theorem unsat212 : Unsatisfiable (PosFin 31) f212 := by
  apply lratCheckerSound f212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p212
  · intro a ha; simp [p212] at ha; subst a; trivial
  · exact checked212
theorem derived212 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c212 := by
  apply localUnsat_implies_entails f212 [c209, c208, c205, c33, c27, c35, c143, c186, c23, c68] c212 unsat212 (by rfl) a
  have h0 : Entails.eval a c209 := derived209 a h
  have h1 : Entails.eval a c208 := derived208 a h
  have h2 : Entails.eval a c205 := derived205 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c186 := derived186 a h
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c213 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f213 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c190, some c205, some c208, some c209, some c210, some c120, some c212, some c5, some c211, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p213 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked213 : lratChecker f213 p213 = .success := by decide +kernel
theorem unsat213 : Unsatisfiable (PosFin 31) f213 := by
  apply lratCheckerSound f213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p213
  · intro a ha; simp [p213] at ha; subst a; trivial
  · exact checked213
theorem derived213 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c213 := by
  apply localUnsat_implies_entails f213 [c190, c205, c208, c209, c210, c120, c212, c5, c211] c213 unsat213 (by rfl) a
  have h0 : Entails.eval a c190 := derived190 a h
  have h1 : Entails.eval a c205 := derived205 a h
  have h2 : Entails.eval a c208 := derived208 a h
  have h3 : Entails.eval a c209 := derived209 a h
  have h4 : Entails.eval a c210 := derived210 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c212 := derived212 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c211 := derived211 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c214 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨19, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f214 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c207, some c210, some c120, some c98, some c9, some c79, some c157, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p214 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked214 : lratChecker f214 p214 = .success := by decide +kernel
theorem unsat214 : Unsatisfiable (PosFin 31) f214 := by
  apply lratCheckerSound f214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p214
  · intro a ha; simp [p214] at ha; subst a; trivial
  · exact checked214
theorem derived214 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c214 := by
  apply localUnsat_implies_entails f214 [c207, c210, c120, c98, c9, c79, c157] c214 unsat214 (by rfl) a
  have h0 : Entails.eval a c207 := derived207 a h
  have h1 : Entails.eval a c210 := derived210 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c215 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f215 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c207, some c33, some c27, some c35, some c143, some c186, some c23, some c68, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p215 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked215 : lratChecker f215 p215 = .success := by decide +kernel
theorem unsat215 : Unsatisfiable (PosFin 31) f215 := by
  apply lratCheckerSound f215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p215
  · intro a ha; simp [p215] at ha; subst a; trivial
  · exact checked215
theorem derived215 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c215 := by
  apply localUnsat_implies_entails f215 [c207, c33, c27, c35, c143, c186, c23, c68] c215 unsat215 (by rfl) a
  have h0 : Entails.eval a c207 := derived207 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c186 := derived186 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c216 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨30, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f216 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c99, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p216 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked216 : lratChecker f216 p216 = .success := by decide +kernel
theorem unsat216 : Unsatisfiable (PosFin 31) f216 := by
  apply lratCheckerSound f216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p216
  · intro a ha; simp [p216] at ha; subst a; trivial
  · exact checked216
theorem derived216 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c216 := by
  apply localUnsat_implies_entails f216 [c214, c99] c216 unsat216 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c217 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f217 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c215, some c5, some c216, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p217 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked217 : lratChecker f217 p217 = .success := by decide +kernel
theorem unsat217 : Unsatisfiable (PosFin 31) f217 := by
  apply lratCheckerSound f217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p217
  · intro a ha; simp [p217] at ha; subst a; trivial
  · exact checked217
theorem derived217 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c217 := by
  apply localUnsat_implies_entails f217 [c215, c5, c216] c217 unsat217 (by rfl) a
  have h0 : Entails.eval a c215 := derived215 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c216 := derived216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c218 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f218 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c217, some c116, some c115, some c213, some c61, some c31, some c10, some c7, some c109, some c88, some c77, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p218 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked218 : lratChecker f218 p218 = .success := by decide +kernel
theorem unsat218 : Unsatisfiable (PosFin 31) f218 := by
  apply lratCheckerSound f218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p218
  · intro a ha; simp [p218] at ha; subst a; trivial
  · exact checked218
theorem derived218 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c218 := by
  apply localUnsat_implies_entails f218 [c217, c116, c115, c213, c61, c31, c10, c7, c109, c88, c77] c218 unsat218 (by rfl) a
  have h0 : Entails.eval a c217 := derived217 a h
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c213 := derived213 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c219 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f219 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c217, some c116, some c218, some c113, some c73, some c74, some c154, some c112, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p219 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked219 : lratChecker f219 p219 = .success := by decide +kernel
theorem unsat219 : Unsatisfiable (PosFin 31) f219 := by
  apply lratCheckerSound f219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p219
  · intro a ha; simp [p219] at ha; subst a; trivial
  · exact checked219
theorem derived219 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c219 := by
  apply localUnsat_implies_entails f219 [c217, c116, c218, c113, c73, c74, c154, c112] c219 unsat219 (by rfl) a
  have h0 : Entails.eval a c217 := derived217 a h
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c218 := derived218 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c220 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f220 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c219, some c217, some c116, some c115, some c14, some c112, some c2, some c55, some c59, some c148, some c29, some c172, some c160, some c168, some c129, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p220 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked220 : lratChecker f220 p220 = .success := by decide +kernel
theorem unsat220 : Unsatisfiable (PosFin 31) f220 := by
  apply lratCheckerSound f220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p220
  · intro a ha; simp [p220] at ha; subst a; trivial
  · exact checked220
theorem derived220 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c220 := by
  apply localUnsat_implies_entails f220 [c219, c217, c116, c115, c14, c112, c2, c55, c59, c148, c29, c172, c160, c168, c129] c220 unsat220 (by rfl) a
  have h0 : Entails.eval a c219 := derived219 a h
  have h1 : Entails.eval a c217 := derived217 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c160 := h 159 (by decide)
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c221 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f221 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c115, some c116, some c220, some c57, some c61, some c31, some c10, some c7, some c45, some c144, some c92, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p221 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked221 : lratChecker f221 p221 = .success := by decide +kernel
theorem unsat221 : Unsatisfiable (PosFin 31) f221 := by
  apply lratCheckerSound f221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p221
  · intro a ha; simp [p221] at ha; subst a; trivial
  · exact checked221
theorem derived221 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c221 := by
  apply localUnsat_implies_entails f221 [c115, c116, c220, c57, c61, c31, c10, c7, c45, c144, c92] c221 unsat221 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c220 := derived220 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c144 := h 143 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c222 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f222 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c217, some c221, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p222 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked222 : lratChecker f222 p222 = .success := by decide +kernel
theorem unsat222 : Unsatisfiable (PosFin 31) f222 := by
  apply lratCheckerSound f222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p222
  · intro a ha; simp [p222] at ha; subst a; trivial
  · exact checked222
theorem derived222 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c222 := by
  apply localUnsat_implies_entails f222 [c217, c221] c222 unsat222 (by rfl) a
  have h0 : Entails.eval a c217 := derived217 a h
  have h1 : Entails.eval a c221 := derived221 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c223 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f223 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c45, some c86, some c8, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p223 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked223 : lratChecker f223 p223 = .success := by decide +kernel
theorem unsat223 : Unsatisfiable (PosFin 31) f223 := by
  apply lratCheckerSound f223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p223
  · intro a ha; simp [p223] at ha; subst a; trivial
  · exact checked223
theorem derived223 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c223 := by
  apply localUnsat_implies_entails f223 [c222, c45, c86, c8] c223 unsat223 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c224 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨28, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f224 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c223, some c61, some c57, some c222, some c119, some c117, some c8, some c96, some c11, some c153, some c81, some c147, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p224 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked224 : lratChecker f224 p224 = .success := by decide +kernel
theorem unsat224 : Unsatisfiable (PosFin 31) f224 := by
  apply lratCheckerSound f224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p224
  · intro a ha; simp [p224] at ha; subst a; trivial
  · exact checked224
theorem derived224 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c224 := by
  apply localUnsat_implies_entails f224 [c223, c61, c57, c222, c119, c117, c8, c96, c11, c153, c81, c147] c224 unsat224 (by rfl) a
  have h0 : Entails.eval a c223 := derived223 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c222 := derived222 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c225 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f225 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c83, some c17, some c8, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p225 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked225 : lratChecker f225 p225 = .success := by decide +kernel
theorem unsat225 : Unsatisfiable (PosFin 31) f225 := by
  apply lratCheckerSound f225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p225
  · intro a ha; simp [p225] at ha; subst a; trivial
  · exact checked225
theorem derived225 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c225 := by
  apply localUnsat_implies_entails f225 [c222, c83, c17, c8] c225 unsat225 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c226 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f226 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c225, some c222, some c213, some c65, some c64, some c7, some c224, some c2, some c200, some c140, some c150, some c141, some c96, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p226 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked226 : lratChecker f226 p226 = .success := by decide +kernel
theorem unsat226 : Unsatisfiable (PosFin 31) f226 := by
  apply lratCheckerSound f226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p226
  · intro a ha; simp [p226] at ha; subst a; trivial
  · exact checked226
theorem derived226 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c226 := by
  apply localUnsat_implies_entails f226 [c225, c222, c213, c65, c64, c7, c224, c2, c200, c140, c150, c141, c96] c226 unsat226 (by rfl) a
  have h0 : Entails.eval a c225 := derived225 a h
  have h1 : Entails.eval a c222 := derived222 a h
  have h2 : Entails.eval a c213 := derived213 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c224 := derived224 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c200 := derived200 a h
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c150 := h 149 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c227 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f227 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c213, some c225, some c226, some c223, some c2, some c200, some c132, some c204, some c3, some c148, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p227 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked227 : lratChecker f227 p227 = .success := by decide +kernel
theorem unsat227 : Unsatisfiable (PosFin 31) f227 := by
  apply lratCheckerSound f227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p227
  · intro a ha; simp [p227] at ha; subst a; trivial
  · exact checked227
theorem derived227 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c227 := by
  apply localUnsat_implies_entails f227 [c222, c213, c225, c226, c223, c2, c200, c132, c204, c3, c148] c227 unsat227 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c213 := derived213 a h
  have h2 : Entails.eval a c225 := derived225 a h
  have h3 : Entails.eval a c226 := derived226 a h
  have h4 : Entails.eval a c223 := derived223 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c200 := derived200 a h
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c204 := derived204 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c228 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f228 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c227, some c222, some c45, some c49, some c69, some c53, some c128, some c62, some c5, some c193, some c12, some c138, some c1, some c20, some c171, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p228 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked228 : lratChecker f228 p228 = .success := by decide +kernel
theorem unsat228 : Unsatisfiable (PosFin 31) f228 := by
  apply lratCheckerSound f228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p228
  · intro a ha; simp [p228] at ha; subst a; trivial
  · exact checked228
theorem derived228 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c228 := by
  apply localUnsat_implies_entails f228 [c227, c222, c45, c49, c69, c53, c128, c62, c5, c193, c12, c138, c1, c20, c171] c228 unsat228 (by rfl) a
  have h0 : Entails.eval a c227 := derived227 a h
  have h1 : Entails.eval a c222 := derived222 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c128 := h 127 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c193 := derived193 a h
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c20 := h 19 (by decide)
  have h14 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c229 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f229 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c227, some c222, some c228, some c8, some c200, some c90, some c57, some c61, some c13, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p229 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked229 : lratChecker f229 p229 = .success := by decide +kernel
theorem unsat229 : Unsatisfiable (PosFin 31) f229 := by
  apply lratCheckerSound f229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p229
  · intro a ha; simp [p229] at ha; subst a; trivial
  · exact checked229
theorem derived229 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c229 := by
  apply localUnsat_implies_entails f229 [c227, c222, c228, c8, c200, c90, c57, c61, c13] c229 unsat229 (by rfl) a
  have h0 : Entails.eval a c227 := derived227 a h
  have h1 : Entails.eval a c222 := derived222 a h
  have h2 : Entails.eval a c228 := derived228 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c200 := derived200 a h
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c230 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f230 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c227, some c222, some c213, some c200, some c57, some c61, some c63, some c99, some c199, some c13, some c194, some c186, some c76, some c121, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p230 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked230 : lratChecker f230 p230 = .success := by decide +kernel
theorem unsat230 : Unsatisfiable (PosFin 31) f230 := by
  apply lratCheckerSound f230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p230
  · intro a ha; simp [p230] at ha; subst a; trivial
  · exact checked230
theorem derived230 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c230 := by
  apply localUnsat_implies_entails f230 [c227, c222, c213, c200, c57, c61, c63, c99, c199, c13, c194, c186, c76, c121] c230 unsat230 (by rfl) a
  have h0 : Entails.eval a c227 := derived227 a h
  have h1 : Entails.eval a c222 := derived222 a h
  have h2 : Entails.eval a c213 := derived213 a h
  have h3 : Entails.eval a c200 := derived200 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c199 := derived199 a h
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c194 := derived194 a h
  have h11 : Entails.eval a c186 := derived186 a h
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c231 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f231 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c227, some c229, some c230, some c202, some c55, some c57, some c41, some c64, some c5, some c87, some c12, some c114, some c155, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p231 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked231 : lratChecker f231 p231 = .success := by decide +kernel
theorem unsat231 : Unsatisfiable (PosFin 31) f231 := by
  apply lratCheckerSound f231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p231
  · intro a ha; simp [p231] at ha; subst a; trivial
  · exact checked231
theorem derived231 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c231 := by
  apply localUnsat_implies_entails f231 [c222, c227, c229, c230, c202, c55, c57, c41, c64, c5, c87, c12, c114, c155] c231 unsat231 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c227 := derived227 a h
  have h2 : Entails.eval a c229 := derived229 a h
  have h3 : Entails.eval a c230 := derived230 a h
  have h4 : Entails.eval a c202 := derived202 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c87 := h 86 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c232 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f232 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c71, some c70, some c146, some c108, some c110, some c23, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p232 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked232 : lratChecker f232 p232 = .success := by decide +kernel
theorem unsat232 : Unsatisfiable (PosFin 31) f232 := by
  apply lratCheckerSound f232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p232
  · intro a ha; simp [p232] at ha; subst a; trivial
  · exact checked232
theorem derived232 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c232 := by
  apply localUnsat_implies_entails f232 [c71, c70, c146, c108, c110, c23] c232 unsat232 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c233 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f233 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c49, some c53, some c12, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p233 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked233 : lratChecker f233 p233 = .success := by decide +kernel
theorem unsat233 : Unsatisfiable (PosFin 31) f233 := by
  apply lratCheckerSound f233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p233
  · intro a ha; simp [p233] at ha; subst a; trivial
  · exact checked233
theorem derived233 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c233 := by
  apply localUnsat_implies_entails f233 [c49, c53, c12] c233 unsat233 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c234 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨2, by decide⟩, true), (⟨28, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f234 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c233, some c232, some c202, some c7, some c191, some c4, some c102, some c114, some c170, some c161, some c19, some c78, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p234 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked234 : lratChecker f234 p234 = .success := by decide +kernel
theorem unsat234 : Unsatisfiable (PosFin 31) f234 := by
  apply lratCheckerSound f234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p234
  · intro a ha; simp [p234] at ha; subst a; trivial
  · exact checked234
theorem derived234 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c234 := by
  apply localUnsat_implies_entails f234 [c231, c233, c232, c202, c7, c191, c4, c102, c114, c170, c161, c19, c78] c234 unsat234 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c233 := derived233 a h
  have h2 : Entails.eval a c232 := derived232 a h
  have h3 : Entails.eval a c202 := derived202 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c191 := derived191 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c235 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨16, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f235 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c146, some c78, some c38, some c26, some c9, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p235 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked235 : lratChecker f235 p235 = .success := by decide +kernel
theorem unsat235 : Unsatisfiable (PosFin 31) f235 := by
  apply lratCheckerSound f235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p235
  · intro a ha; simp [p235] at ha; subst a; trivial
  · exact checked235
theorem derived235 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c235 := by
  apply localUnsat_implies_entails f235 [c231, c146, c78, c38, c26, c9] c235 unsat235 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c236 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨28, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f236 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c202, some c233, some c234, some c235, some c47, some c51, some c12, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p236 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked236 : lratChecker f236 p236 = .success := by decide +kernel
theorem unsat236 : Unsatisfiable (PosFin 31) f236 := by
  apply lratCheckerSound f236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p236
  · intro a ha; simp [p236] at ha; subst a; trivial
  · exact checked236
theorem derived236 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c236 := by
  apply localUnsat_implies_entails f236 [c202, c233, c234, c235, c47, c51, c12] c236 unsat236 (by rfl) a
  have h0 : Entails.eval a c202 := derived202 a h
  have h1 : Entails.eval a c233 := derived233 a h
  have h2 : Entails.eval a c234 := derived234 a h
  have h3 : Entails.eval a c235 := derived235 a h
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c237 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f237 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c47, some c51, some c145, some c158, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p237 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked237 : lratChecker f237 p237 = .success := by decide +kernel
theorem unsat237 : Unsatisfiable (PosFin 31) f237 := by
  apply lratCheckerSound f237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p237
  · intro a ha; simp [p237] at ha; subst a; trivial
  · exact checked237
theorem derived237 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c237 := by
  apply localUnsat_implies_entails f237 [c47, c51, c145, c158] c237 unsat237 (by rfl) a
  have h0 : Entails.eval a c47 := h 46 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c238 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨22, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f238 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c237, some c146, some c38, some c34, some c163, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p238 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked238 : lratChecker f238 p238 = .success := by decide +kernel
theorem unsat238 : Unsatisfiable (PosFin 31) f238 := by
  apply lratCheckerSound f238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p238
  · intro a ha; simp [p238] at ha; subst a; trivial
  · exact checked238
theorem derived238 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c238 := by
  apply localUnsat_implies_entails f238 [c237, c146, c38, c34, c163] c238 unsat238 (by rfl) a
  have h0 : Entails.eval a c237 := derived237 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c239 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f239 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c18, some c134, some c4, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p239 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked239 : lratChecker f239 p239 = .success := by decide +kernel
theorem unsat239 : Unsatisfiable (PosFin 31) f239 := by
  apply lratCheckerSound f239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p239
  · intro a ha; simp [p239] at ha; subst a; trivial
  · exact checked239
theorem derived239 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c239 := by
  apply localUnsat_implies_entails f239 [c231, c18, c134, c4] c239 unsat239 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c240 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f240 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c236, some c239, some c74, some c75, some c5, some c158, some c111, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p240 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked240 : lratChecker f240 p240 = .success := by decide +kernel
theorem unsat240 : Unsatisfiable (PosFin 31) f240 := by
  apply lratCheckerSound f240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p240
  · intro a ha; simp [p240] at ha; subst a; trivial
  · exact checked240
theorem derived240 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c240 := by
  apply localUnsat_implies_entails f240 [c236, c239, c74, c75, c5, c158, c111] c240 unsat240 (by rfl) a
  have h0 : Entails.eval a c236 := derived236 a h
  have h1 : Entails.eval a c239 := derived239 a h
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c241 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f241 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c90, some c122, some c7, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p241 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked241 : lratChecker f241 p241 = .success := by decide +kernel
theorem unsat241 : Unsatisfiable (PosFin 31) f241 := by
  apply lratCheckerSound f241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p241
  · intro a ha; simp [p241] at ha; subst a; trivial
  · exact checked241
theorem derived241 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c241 := by
  apply localUnsat_implies_entails f241 [c90, c122, c7] c241 unsat241 (by rfl) a
  have h0 : Entails.eval a c90 := h 89 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c242 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f242 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c202, some c240, some c101, some c191, some c241, some c233, some c238, some c7, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p242 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked242 : lratChecker f242 p242 = .success := by decide +kernel
theorem unsat242 : Unsatisfiable (PosFin 31) f242 := by
  apply lratCheckerSound f242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p242
  · intro a ha; simp [p242] at ha; subst a; trivial
  · exact checked242
theorem derived242 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c242 := by
  apply localUnsat_implies_entails f242 [c202, c240, c101, c191, c241, c233, c238, c7] c242 unsat242 (by rfl) a
  have h0 : Entails.eval a c202 := derived202 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c191 := derived191 a h
  have h4 : Entails.eval a c241 := derived241 a h
  have h5 : Entails.eval a c233 := derived233 a h
  have h6 : Entails.eval a c238 := derived238 a h
  have h7 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c243 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, true), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f243 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c7, some c242, some c8, some c192, some c56, some c40, some c152, some c10, some c5, some c137, some c165, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p243 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked243 : lratChecker f243 p243 = .success := by decide +kernel
theorem unsat243 : Unsatisfiable (PosFin 31) f243 := by
  apply lratCheckerSound f243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p243
  · intro a ha; simp [p243] at ha; subst a; trivial
  · exact checked243
theorem derived243 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c243 := by
  apply localUnsat_implies_entails f243 [c7, c242, c8, c192, c56, c40, c152, c10, c5, c137, c165] c243 unsat243 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c242 := derived242 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c192 := derived192 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c244 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨4, by decide⟩, true), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f244 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c242, some c7, some c243, some c68, some c197, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p244 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked244 : lratChecker f244 p244 = .success := by decide +kernel
theorem unsat244 : Unsatisfiable (PosFin 31) f244 := by
  apply lratCheckerSound f244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p244
  · intro a ha; simp [p244] at ha; subst a; trivial
  · exact checked244
theorem derived244 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c244 := by
  apply localUnsat_implies_entails f244 [c242, c7, c243, c68, c197] c244 unsat244 (by rfl) a
  have h0 : Entails.eval a c242 := derived242 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c243 := derived243 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c197 := derived197 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c245 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f245 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c242, some c199, some c194, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p245 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked245 : lratChecker f245 p245 = .success := by decide +kernel
theorem unsat245 : Unsatisfiable (PosFin 31) f245 := by
  apply lratCheckerSound f245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p245
  · intro a ha; simp [p245] at ha; subst a; trivial
  · exact checked245
theorem derived245 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c245 := by
  apply localUnsat_implies_entails f245 [c242, c199, c194] c245 unsat245 (by rfl) a
  have h0 : Entails.eval a c242 := derived242 a h
  have h1 : Entails.eval a c199 := derived199 a h
  have h2 : Entails.eval a c194 := derived194 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c246 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f246 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c242, some c8, some c244, some c245, some c192, some c56, some c25, some c152, some c5, some c9, some c136, some c166, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p246 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked246 : lratChecker f246 p246 = .success := by decide +kernel
theorem unsat246 : Unsatisfiable (PosFin 31) f246 := by
  apply lratCheckerSound f246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p246
  · intro a ha; simp [p246] at ha; subst a; trivial
  · exact checked246
theorem derived246 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c246 := by
  apply localUnsat_implies_entails f246 [c242, c8, c244, c245, c192, c56, c25, c152, c5, c9, c136, c166] c246 unsat246 (by rfl) a
  have h0 : Entails.eval a c242 := derived242 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c244 := derived244 a h
  have h3 : Entails.eval a c245 := derived245 a h
  have h4 : Entails.eval a c192 := derived192 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c136 := h 135 (by decide)
  have h11 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c247 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f247 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c199, some c245, some c66, some c197, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p247 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked247 : lratChecker f247 p247 = .success := by decide +kernel
theorem unsat247 : Unsatisfiable (PosFin 31) f247 := by
  apply lratCheckerSound f247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p247
  · intro a ha; simp [p247] at ha; subst a; trivial
  · exact checked247
theorem derived247 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c247 := by
  apply localUnsat_implies_entails f247 [c199, c245, c66, c197] c247 unsat247 (by rfl) a
  have h0 : Entails.eval a c199 := derived199 a h
  have h1 : Entails.eval a c245 := derived245 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c197 := derived197 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c248 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f248 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c242, some c8, some c247, some c192, some c191, some c246, some c14, some c2, some c54, some c167, some c162, some c159, some c21, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p248 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked248 : lratChecker f248 p248 = .success := by decide +kernel
theorem unsat248 : Unsatisfiable (PosFin 31) f248 := by
  apply lratCheckerSound f248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p248
  · intro a ha; simp [p248] at ha; subst a; trivial
  · exact checked248
theorem derived248 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c248 := by
  apply localUnsat_implies_entails f248 [c231, c242, c8, c247, c192, c191, c246, c14, c2, c54, c167, c162, c159, c21] c248 unsat248 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c242 := derived242 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c247 := derived247 a h
  have h4 : Entails.eval a c192 := derived192 a h
  have h5 : Entails.eval a c191 := derived191 a h
  have h6 : Entails.eval a c246 := derived246 a h
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c249 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f249 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c241, some c2, some c142, some c135, some c7, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p249 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked249 : lratChecker f249 p249 = .success := by decide +kernel
theorem unsat249 : Unsatisfiable (PosFin 31) f249 := by
  apply lratCheckerSound f249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p249
  · intro a ha; simp [p249] at ha; subst a; trivial
  · exact checked249
theorem derived249 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c249 := by
  apply localUnsat_implies_entails f249 [c241, c2, c142, c135, c7] c249 unsat249 (by rfl) a
  have h0 : Entails.eval a c241 := derived241 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c135 := h 134 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c250 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f250 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c242, some c8, some c247, some c191, some c248, some c249, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p250 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked250 : lratChecker f250 p250 = .success := by decide +kernel
theorem unsat250 : Unsatisfiable (PosFin 31) f250 := by
  apply lratCheckerSound f250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p250
  · intro a ha; simp [p250] at ha; subst a; trivial
  · exact checked250
theorem derived250 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c250 := by
  apply localUnsat_implies_entails f250 [c242, c8, c247, c191, c248, c249] c250 unsat250 (by rfl) a
  have h0 : Entails.eval a c242 := derived242 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c247 := derived247 a h
  have h3 : Entails.eval a c191 := derived191 a h
  have h4 : Entails.eval a c248 := derived248 a h
  have h5 : Entails.eval a c249 := derived249 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c251 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f251 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c8, some c250, some c4, some c130, some c100, some c101, some c14, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p251 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked251 : lratChecker f251 p251 = .success := by decide +kernel
theorem unsat251 : Unsatisfiable (PosFin 31) f251 := by
  apply lratCheckerSound f251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p251
  · intro a ha; simp [p251] at ha; subst a; trivial
  · exact checked251
theorem derived251 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c251 := by
  apply localUnsat_implies_entails f251 [c231, c8, c250, c4, c130, c100, c101, c14] c251 unsat251 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c250 := derived250 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c252 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, false), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f252 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c74, some c75, some c2, some c14, some c91, some c149, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p252 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked252 : lratChecker f252 p252 = .success := by decide +kernel
theorem unsat252 : Unsatisfiable (PosFin 31) f252 := by
  apply lratCheckerSound f252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p252
  · intro a ha; simp [p252] at ha; subst a; trivial
  · exact checked252
theorem derived252 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c252 := by
  apply localUnsat_implies_entails f252 [c231, c74, c75, c2, c14, c91, c149] c252 unsat252 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c253 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f253 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c250, some c249, some c4, some c8, some c130, some c251, some c252, some c103, some c123, some c151, some c15, some c84, some c117, some c7, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p253 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked253 : lratChecker f253 p253 = .success := by decide +kernel
theorem unsat253 : Unsatisfiable (PosFin 31) f253 := by
  apply lratCheckerSound f253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p253
  · intro a ha; simp [p253] at ha; subst a; trivial
  · exact checked253
theorem derived253 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c253 := by
  apply localUnsat_implies_entails f253 [c231, c250, c249, c4, c8, c130, c251, c252, c103, c123, c151, c15, c84, c117, c7] c253 unsat253 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c250 := derived250 a h
  have h2 : Entails.eval a c249 := derived249 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c130 := h 129 (by decide)
  have h6 : Entails.eval a c251 := derived251 a h
  have h7 : Entails.eval a c252 := derived252 a h
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c151 := h 150 (by decide)
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c254 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f254 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c250, some c253, some c17, some c239, some c8, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p254 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked254 : lratChecker f254 p254 = .success := by decide +kernel
theorem unsat254 : Unsatisfiable (PosFin 31) f254 := by
  apply lratCheckerSound f254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p254
  · intro a ha; simp [p254] at ha; subst a; trivial
  · exact checked254
theorem derived254 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c254 := by
  apply localUnsat_implies_entails f254 [c250, c253, c17, c239, c8] c254 unsat254 (by rfl) a
  have h0 : Entails.eval a c250 := derived250 a h
  have h1 : Entails.eval a c253 := derived253 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c255 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f255 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c250, some c17, some c4, some c8, some c131, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p255 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked255 : lratChecker f255 p255 = .success := by decide +kernel
theorem unsat255 : Unsatisfiable (PosFin 31) f255 := by
  apply lratCheckerSound f255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p255
  · intro a ha; simp [p255] at ha; subst a; trivial
  · exact checked255
theorem derived255 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c255 := by
  apply localUnsat_implies_entails f255 [c231, c250, c17, c4, c8, c131] c255 unsat255 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c250 := derived250 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c256 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f256 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c231, some c255, some c254, some c250, some c4, some c8, some c130, some c232, some c252, some c103, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p256 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked256 : lratChecker f256 p256 = .success := by decide +kernel
theorem unsat256 : Unsatisfiable (PosFin 31) f256 := by
  apply lratCheckerSound f256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p256
  · intro a ha; simp [p256] at ha; subst a; trivial
  · exact checked256
theorem derived256 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c256 := by
  apply localUnsat_implies_entails f256 [c231, c255, c254, c250, c4, c8, c130, c232, c252, c103] c256 unsat256 (by rfl) a
  have h0 : Entails.eval a c231 := derived231 a h
  have h1 : Entails.eval a c255 := derived255 a h
  have h2 : Entails.eval a c254 := derived254 a h
  have h3 : Entails.eval a c250 := derived250 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c232 := derived232 a h
  have h8 : Entails.eval a c252 := derived252 a h
  have h9 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c257 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f257 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c256, some c255, some c250, some c119, some c86, some c7, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p257 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked257 : lratChecker f257 p257 = .success := by decide +kernel
theorem unsat257 : Unsatisfiable (PosFin 31) f257 := by
  apply lratCheckerSound f257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p257
  · intro a ha; simp [p257] at ha; subst a; trivial
  · exact checked257
theorem derived257 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c257 := by
  apply localUnsat_implies_entails f257 [c256, c255, c250, c119, c86, c7] c257 unsat257 (by rfl) a
  have h0 : Entails.eval a c256 := derived256 a h
  have h1 : Entails.eval a c255 := derived255 a h
  have h2 : Entails.eval a c250 := derived250 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c258 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f258 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c250, some c255, some c256, some c16, some c257, some c2, some c14, some c195, some c133, some c141, some c118, some c23, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p258 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked258 : lratChecker f258 p258 = .success := by decide +kernel
theorem unsat258 : Unsatisfiable (PosFin 31) f258 := by
  apply lratCheckerSound f258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p258
  · intro a ha; simp [p258] at ha; subst a; trivial
  · exact checked258
theorem derived258 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c258 := by
  apply localUnsat_implies_entails f258 [c250, c255, c256, c16, c257, c2, c14, c195, c133, c141, c118, c23] c258 unsat258 (by rfl) a
  have h0 : Entails.eval a c250 := derived250 a h
  have h1 : Entails.eval a c255 := derived255 a h
  have h2 : Entails.eval a c256 := derived256 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c257 := derived257 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c195 := derived195 a h
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c259 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f259 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c37, some c39, some c164, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p259 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked259 : lratChecker f259 p259 = .success := by decide +kernel
theorem unsat259 : Unsatisfiable (PosFin 31) f259 := by
  apply lratCheckerSound f259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p259
  · intro a ha; simp [p259] at ha; subst a; trivial
  · exact checked259
theorem derived259 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c259 := by
  apply localUnsat_implies_entails f259 [c258, c37, c39, c164] c259 unsat259 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c260 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f260 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c22, some c33, some c35, some c164, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p260 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked260 : lratChecker f260 p260 = .success := by decide +kernel
theorem unsat260 : Unsatisfiable (PosFin 31) f260 := by
  apply lratCheckerSound f260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p260
  · intro a ha; simp [p260] at ha; subst a; trivial
  · exact checked260
theorem derived260 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c260 := by
  apply localUnsat_implies_entails f260 [c258, c22, c33, c35, c164] c260 unsat260 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c261 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f261 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c259, some c260, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p261 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked261 : lratChecker f261 p261 = .success := by decide +kernel
theorem unsat261 : Unsatisfiable (PosFin 31) f261 := by
  apply lratCheckerSound f261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p261
  · intro a ha; simp [p261] at ha; subst a; trivial
  · exact checked261
theorem derived261 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c261 := by
  apply localUnsat_implies_entails f261 [c259, c260] c261 unsat261 (by rfl) a
  have h0 : Entails.eval a c259 := derived259 a h
  have h1 : Entails.eval a c260 := derived260 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c262 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f262 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c33, some c35, some c156, some c143, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p262 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked262 : lratChecker f262 p262 = .success := by decide +kernel
theorem unsat262 : Unsatisfiable (PosFin 31) f262 := by
  apply lratCheckerSound f262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p262
  · intro a ha; simp [p262] at ha; subst a; trivial
  · exact checked262
theorem derived262 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c262 := by
  apply localUnsat_implies_entails f262 [c258, c33, c35, c156, c143] c262 unsat262 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c263 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f263 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c262, some c154, some c52, some c50, some c163, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p263 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked263 : lratChecker f263 p263 = .success := by decide +kernel
theorem unsat263 : Unsatisfiable (PosFin 31) f263 := by
  apply lratCheckerSound f263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p263
  · intro a ha; simp [p263] at ha; subst a; trivial
  · exact checked263
theorem derived263 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c263 := by
  apply localUnsat_implies_entails f263 [c262, c154, c52, c50, c163] c263 unsat263 (by rfl) a
  have h0 : Entails.eval a c262 := derived262 a h
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c264 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f264 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c263, some c37, some c39, some c143, some c7, some c52, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p264 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked264 : lratChecker f264 p264 = .success := by decide +kernel
theorem unsat264 : Unsatisfiable (PosFin 31) f264 := by
  apply lratCheckerSound f264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p264
  · intro a ha; simp [p264] at ha; subst a; trivial
  · exact checked264
theorem derived264 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c264 := by
  apply localUnsat_implies_entails f264 [c258, c263, c37, c39, c143, c7, c52] c264 unsat264 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c263 := derived263 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c265 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f265 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c48, some c157, some c46, some c7, some c163, some c35, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p265 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked265 : lratChecker f265 p265 = .success := by decide +kernel
theorem unsat265 : Unsatisfiable (PosFin 31) f265 := by
  apply lratCheckerSound f265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p265
  · intro a ha; simp [p265] at ha; subst a; trivial
  · exact checked265
theorem derived265 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c265 := by
  apply localUnsat_implies_entails f265 [c258, c48, c157, c46, c7, c163, c35] c265 unsat265 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c266 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f266 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c33, some c35, some c143, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p266 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked266 : lratChecker f266 p266 = .success := by decide +kernel
theorem unsat266 : Unsatisfiable (PosFin 31) f266 := by
  apply lratCheckerSound f266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p266
  · intro a ha; simp [p266] at ha; subst a; trivial
  · exact checked266
theorem derived266 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c266 := by
  apply localUnsat_implies_entails f266 [c258, c33, c35, c143] c266 unsat266 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c267 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f267 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c154, some c37, some c39, some c143, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p267 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked267 : lratChecker f267 p267 = .success := by decide +kernel
theorem unsat267 : Unsatisfiable (PosFin 31) f267 := by
  apply lratCheckerSound f267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p267
  · intro a ha; simp [p267] at ha; subst a; trivial
  · exact checked267
theorem derived267 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c267 := by
  apply localUnsat_implies_entails f267 [c258, c154, c37, c39, c143] c267 unsat267 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c268 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f268 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c267, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p268 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked268 : lratChecker f268 p268 = .success := by decide +kernel
theorem unsat268 : Unsatisfiable (PosFin 31) f268 := by
  apply lratCheckerSound f268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p268
  · intro a ha; simp [p268] at ha; subst a; trivial
  · exact checked268
theorem derived268 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c268 := by
  apply localUnsat_implies_entails f268 [c266, c267] c268 unsat268 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c267 := derived267 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c269 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f269 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c264, some c261, some c265, some c268, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p269 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked269 : lratChecker f269 p269 = .success := by decide +kernel
theorem unsat269 : Unsatisfiable (PosFin 31) f269 := by
  apply lratCheckerSound f269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p269
  · intro a ha; simp [p269] at ha; subst a; trivial
  · exact checked269
theorem derived269 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c269 := by
  apply localUnsat_implies_entails f269 [c264, c261, c265, c268] c269 unsat269 (by rfl) a
  have h0 : Entails.eval a c264 := derived264 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c265 := derived265 a h
  have h3 : Entails.eval a c268 := derived268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c270 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f270 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c269, some c47, some c49, some c7, some c35, some c39, some c163, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p270 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked270 : lratChecker f270 p270 = .success := by decide +kernel
theorem unsat270 : Unsatisfiable (PosFin 31) f270 := by
  apply lratCheckerSound f270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p270
  · intro a ha; simp [p270] at ha; subst a; trivial
  · exact checked270
theorem derived270 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c270 := by
  apply localUnsat_implies_entails f270 [c258, c269, c47, c49, c7, c35, c39, c163] c270 unsat270 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c269 := derived269 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c271 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f271 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c269, some c270, some c261, some c51, some c53, some c7, some c35, some c39, some c163, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p271 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked271 : lratChecker f271 p271 = .success := by decide +kernel
theorem unsat271 : Unsatisfiable (PosFin 31) f271 := by
  apply lratCheckerSound f271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p271
  · intro a ha; simp [p271] at ha; subst a; trivial
  · exact checked271
theorem derived271 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c271 := by
  apply localUnsat_implies_entails f271 [c258, c269, c270, c261, c51, c53, c7, c35, c39, c163] c271 unsat271 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c269 := derived269 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c261 := derived261 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c272 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f272 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c271, some c231, some c17, some c139, some c4, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p272 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked272 : lratChecker f272 p272 = .success := by decide +kernel
theorem unsat272 : Unsatisfiable (PosFin 31) f272 := by
  apply lratCheckerSound f272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p272
  · intro a ha; simp [p272] at ha; subst a; trivial
  · exact checked272
theorem derived272 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c272 := by
  apply localUnsat_implies_entails f272 [c258, c271, c231, c17, c139, c4] c272 unsat272 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c271 := derived271 a h
  have h2 : Entails.eval a c231 := derived231 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived272

end CochromaticTwenty.Certificates.Z12Direct_5_7_10
