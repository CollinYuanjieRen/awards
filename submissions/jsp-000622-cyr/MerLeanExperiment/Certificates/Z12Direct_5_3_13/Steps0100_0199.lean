import MerLeanExperiment.Certificates.Z12Direct_5_3_13.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_3_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c505 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c303, some c275, some c241, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p505 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 31) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c491, c303, c275, c241] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  have h3 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c283, some c496, some c500, some c503, some c102, some c505, some c34, some c169, some c252, some c166, some c130, some c181, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p506 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 31) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c491, c283, c496, c500, c503, c102, c505, c34, c169, c252, c166, c130, c181] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c496 := derived496 a h
  have h3 : Entails.eval a c500 := derived500 a h
  have h4 : Entails.eval a c503 := derived503 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c505 := derived505 a h
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c166 := h 165 (by decide)
  have h11 : Entails.eval a c130 := h 129 (by decide)
  have h12 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c506, some c252, some c166, some c130, some c466, some c26, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p507 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 31) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c491, c506, c252, c166, c130, c466, c26] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c466 := derived466 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c506, some c169, some c507, some c149, some c179, some c69, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p508 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 31) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c491, c506, c169, c507, c149, c179, c69] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c169 := h 168 (by decide)
  have h3 : Entails.eval a c507 := derived507 a h
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c508, some c4, some c505, some c29, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p509 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 31) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c508, c4, c505, c29] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c505 := derived505 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c510 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c4, some c336, some c29, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p510 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 31) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c4, c336, c29] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c506, some c509, some c212, some c70, some c69, some c67, some c287, some c313, some c250, some c380, some c510, some c179, some c39, some c190, some c252, some c369, some c293, some c201, some c306, some c182, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p511 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 31) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c491, c506, c509, c212, c70, c69, c67, c287, c313, c250, c380, c510, c179, c39, c190, c252, c369, c293, c201, c306, c182] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c509 := derived509 a h
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c287 := h 286 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c380 := h 379 (by decide)
  have h11 : Entails.eval a c510 := derived510 a h
  have h12 : Entails.eval a c179 := h 178 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c190 := h 189 (by decide)
  have h15 : Entails.eval a c252 := h 251 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c293 := h 292 (by decide)
  have h18 : Entails.eval a c201 := h 200 (by decide)
  have h19 : Entails.eval a c306 := h 305 (by decide)
  have h20 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c511, some c506, some c212, some c70, some c69, some c67, some c287, some c313, some c114, some c54, some c250, some c380, some c133, some c337, some c394, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p512 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 31) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c491, c511, c506, c212, c70, c69, c67, c287, c313, c114, c54, c250, c380, c133, c337, c394] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c506 := derived506 a h
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c287 := h 286 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c250 := h 249 (by decide)
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  have h14 : Entails.eval a c337 := h 336 (by decide)
  have h15 : Entails.eval a c394 := h 393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c97, some c12, some c69, some c26, some c466, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p513 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 31) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c491, c97, c12, c69, c26, c466] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c466 := derived466 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c514 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f514 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c506, some c511, some c512, some c102, some c399, some c513, some c22, some c114, some c69, some c318, some c70, some c130, some c466, some c20, some c316, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p514 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked514 : lratChecker f514 p514 = .success := by decide +kernel
theorem unsat514 : Unsatisfiable (PosFin 31) f514 := by
  apply lratCheckerSound f514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p514
  · intro a ha; simp [p514] at ha; subst a; trivial
  · exact checked514
theorem derived514 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c514 := by
  apply localUnsat_implies_entails f514 [c491, c506, c511, c512, c102, c399, c513, c22, c114, c69, c318, c70, c130, c466, c20, c316] c514 unsat514 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c511 := derived511 a h
  have h3 : Entails.eval a c512 := derived512 a h
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c399 := h 398 (by decide)
  have h6 : Entails.eval a c513 := derived513 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c130 := h 129 (by decide)
  have h13 : Entails.eval a c466 := derived466 a h
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c515 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨27, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f515 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c69, some c213, some c73, some c250, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p515 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked515 : lratChecker f515 p515 = .success := by decide +kernel
theorem unsat515 : Unsatisfiable (PosFin 31) f515 := by
  apply lratCheckerSound f515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p515
  · intro a ha; simp [p515] at ha; subst a; trivial
  · exact checked515
theorem derived515 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c515 := by
  apply localUnsat_implies_entails f515 [c491, c69, c213, c73, c250] c515 unsat515 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c213 := h 212 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c516 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f516 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c514, some c501, some c506, some c515, some c70, some c76, some c356, some c130, some c284, some c466, some c247, some c316, some c45, some c107, some c143, some c371, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p516 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked516 : lratChecker f516 p516 = .success := by decide +kernel
theorem unsat516 : Unsatisfiable (PosFin 31) f516 := by
  apply lratCheckerSound f516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p516
  · intro a ha; simp [p516] at ha; subst a; trivial
  · exact checked516
theorem derived516 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c516 := by
  apply localUnsat_implies_entails f516 [c491, c514, c501, c506, c515, c70, c76, c356, c130, c284, c466, c247, c316, c45, c107, c143, c371] c516 unsat516 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c514 := derived514 a h
  have h2 : Entails.eval a c501 := derived501 a h
  have h3 : Entails.eval a c506 := derived506 a h
  have h4 : Entails.eval a c515 := derived515 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c466 := derived466 a h
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c143 := h 142 (by decide)
  have h16 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c517 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f517 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c514, some c506, some c501, some c516, some c212, some c70, some c69, some c287, some c140, some c123, some c54, some c109, some c445, some c124, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p517 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked517 : lratChecker f517 p517 = .success := by decide +kernel
theorem unsat517 : Unsatisfiable (PosFin 31) f517 := by
  apply lratCheckerSound f517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p517
  · intro a ha; simp [p517] at ha; subst a; trivial
  · exact checked517
theorem derived517 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c517 := by
  apply localUnsat_implies_entails f517 [c491, c514, c506, c501, c516, c212, c70, c69, c287, c140, c123, c54, c109, c445, c124] c517 unsat517 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c514 := derived514 a h
  have h2 : Entails.eval a c506 := derived506 a h
  have h3 : Entails.eval a c501 := derived501 a h
  have h4 : Entails.eval a c516 := derived516 a h
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c287 := h 286 (by decide)
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c445 := derived445 a h
  have h14 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c518 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f518 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c517, some c514, some c506, some c212, some c70, some c69, some c67, some c287, some c215, some c313, some c37, some c250, some c5, some c33, some c445, some c20, some c309, some c291, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p518 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked518 : lratChecker f518 p518 = .success := by decide +kernel
theorem unsat518 : Unsatisfiable (PosFin 31) f518 := by
  apply lratCheckerSound f518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p518
  · intro a ha; simp [p518] at ha; subst a; trivial
  · exact checked518
theorem derived518 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c518 := by
  apply localUnsat_implies_entails f518 [c491, c517, c514, c506, c212, c70, c69, c67, c287, c215, c313, c37, c250, c5, c33, c445, c20, c309, c291] c518 unsat518 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c517 := derived517 a h
  have h2 : Entails.eval a c514 := derived514 a h
  have h3 : Entails.eval a c506 := derived506 a h
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c287 := h 286 (by decide)
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c250 := h 249 (by decide)
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c445 := derived445 a h
  have h16 : Entails.eval a c20 := h 19 (by decide)
  have h17 : Entails.eval a c309 := h 308 (by decide)
  have h18 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c519 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c506, some c514, some c517, some c518, some c515, some c70, some c356, some c130, some c284, some c466, some c247, some c316, some c20, some c141, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p519 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 31) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c491, c506, c514, c517, c518, c515, c70, c356, c130, c284, c466, c247, c316, c20, c141] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c514 := derived514 a h
  have h3 : Entails.eval a c517 := derived517 a h
  have h4 : Entails.eval a c518 := derived518 a h
  have h5 : Entails.eval a c515 := derived515 a h
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c466 := derived466 a h
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c20 := h 19 (by decide)
  have h14 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨28, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c282, some c210, some c515, some c466, some c377, some c380, some c316, some c129, some c75, some c141, some c497, some c147, some c320, some c257, some c260, some c273, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p520 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 31) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c491, c519, c282, c210, c515, c466, c377, c380, c316, c129, c75, c141, c497, c147, c320, c257, c260, c273] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c282 := h 281 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c515 := derived515 a h
  have h5 : Entails.eval a c466 := derived466 a h
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c497 := derived497 a h
  have h13 : Entails.eval a c147 := h 146 (by decide)
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c260 := h 259 (by decide)
  have h17 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c515, some c519, some c282, some c466, some c377, some c129, some c520, some c26, some c152, some c29, some c12, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p521 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 31) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c491, c515, c519, c282, c466, c377, c129, c520, c26, c152, c29, c12] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c515 := derived515 a h
  have h2 : Entails.eval a c519 := derived519 a h
  have h3 : Entails.eval a c282 := h 281 (by decide)
  have h4 : Entails.eval a c466 := derived466 a h
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c520 := derived520 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c522 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c515, some c521, some c214, some c233, some c25, some c232, some c4, some c14, some c243, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p522 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 31) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c515, c521, c214, c233, c25, c232, c4, c14, c243] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c515 := derived515 a h
  have h1 : Entails.eval a c521 := derived521 a h
  have h2 : Entails.eval a c214 := h 213 (by decide)
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c523 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c515, some c521, some c73, some c214, some c316, some c315, some c522, some c141, some c19, some c343, some c4, some c14, some c341, some c352, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p523 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 31) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c515, c521, c73, c214, c316, c315, c522, c141, c19, c343, c4, c14, c341, c352] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c515 := derived515 a h
  have h1 : Entails.eval a c521 := derived521 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c522 := derived522 a h
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c341 := h 340 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c524 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c377, some c66, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p524 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 31) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c377, c66] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c525 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c44, some c45, some c33, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p525 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 31) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c44, c45, c33] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c523, some c519, some c73, some c214, some c524, some c71, some c378, some c314, some c525, some c186, some c233, some c25, some c294, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p526 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 31) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c523, c519, c73, c214, c524, c71, c378, c314, c525, c186, c233, c25, c294] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c523 := derived523 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c524 := derived524 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c525 := derived525 a h
  have h9 : Entails.eval a c186 := h 185 (by decide)
  have h10 : Entails.eval a c233 := h 232 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c282, some c71, some c311, some c377, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p527 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 31) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c491, c282, c71, c311, c377] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c528 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c523, some c527, some c526, some c495, some c25, some c252, some c4, some c169, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p528 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 31) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c491, c519, c523, c527, c526, c495, c25, c252, c4, c169] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c523 := derived523 a h
  have h3 : Entails.eval a c527 := derived527 a h
  have h4 : Entails.eval a c526 := derived526 a h
  have h5 : Entails.eval a c495 := derived495 a h
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c523, some c527, some c526, some c528, some c215, some c73, some c377, some c378, some c158, some c36, some c389, some c280, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p529 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 31) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c491, c519, c523, c527, c526, c528, c215, c73, c377, c378, c158, c36, c389, c280] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c523 := derived523 a h
  have h3 : Entails.eval a c527 := derived527 a h
  have h4 : Entails.eval a c526 := derived526 a h
  have h5 : Entails.eval a c528 := derived528 a h
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c389 := h 388 (by decide)
  have h13 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c523, some c527, some c526, some c528, some c215, some c529, some c44, some c231, some c33, some c307, some c196, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p530 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 31) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c491, c519, c523, c527, c526, c528, c215, c529, c44, c231, c33, c307, c196] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c523 := derived523 a h
  have h3 : Entails.eval a c527 := derived527 a h
  have h4 : Entails.eval a c526 := derived526 a h
  have h5 : Entails.eval a c528 := derived528 a h
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c529 := derived529 a h
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c231 := h 230 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c307 := h 306 (by decide)
  have h12 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c530, some c519, some c354, some c71, some c67, some c282, some c65, some c314, some c378, some c251, some c186, some c141, some c19, some c343, some c342, some c4, some c328, some c85, some c178, some c297, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p531 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 31) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c491, c530, c519, c354, c71, c67, c282, c65, c314, c378, c251, c186, c141, c19, c343, c342, c4, c328, c85, c178, c297] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c530 := derived530 a h
  have h2 : Entails.eval a c519 := derived519 a h
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c282 := h 281 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c186 := h 185 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c342 := h 341 (by decide)
  have h16 : Entails.eval a c4 := h 3 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c85 := h 84 (by decide)
  have h19 : Entails.eval a c178 := h 177 (by decide)
  have h20 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c530, some c354, some c71, some c67, some c282, some c65, some c314, some c378, some c251, some c531, some c495, some c106, some c19, some c343, some c342, some c328, some c253, some c85, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p532 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 31) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c491, c519, c530, c354, c71, c67, c282, c65, c314, c378, c251, c531, c495, c106, c19, c343, c342, c328, c253, c85] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c530 := derived530 a h
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c282 := h 281 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c531 := derived531 a h
  have h12 : Entails.eval a c495 := derived495 a h
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c343 := h 342 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c253 := h 252 (by decide)
  have h19 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨23, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c221, some c207, some c206, some c205, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p533 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 31) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c491, c221, c207, c206, c205] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c206 := h 205 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c530, some c532, some c212, some c519, some c354, some c533, some c270, some c227, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p534 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 31) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c491, c530, c532, c212, c519, c354, c533, c270, c227] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c530 := derived530 a h
  have h2 : Entails.eval a c532 := derived532 a h
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c519 := derived519 a h
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c533 := derived533 a h
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c532, some c519, some c530, some c354, some c534, some c67, some c287, some c380, some c75, some c250, some c179, some c42, some c252, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p535 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 31) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c491, c532, c519, c530, c354, c534, c67, c287, c380, c75, c250, c179, c42, c252] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c532 := derived532 a h
  have h2 : Entails.eval a c519 := derived519 a h
  have h3 : Entails.eval a c530 := derived530 a h
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c534 := derived534 a h
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c287 := h 286 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c179 := h 178 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c282, some c210, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p536 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 31) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c491, c282, c210] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c530, some c532, some c212, some c536, some c535, some c354, some c358, some c141, some c19, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p537 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 31) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c491, c519, c530, c532, c212, c536, c535, c354, c358, c141, c19] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c530 := derived530 a h
  have h3 : Entails.eval a c532 := derived532 a h
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c536 := derived536 a h
  have h6 : Entails.eval a c535 := derived535 a h
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c530, some c532, some c212, some c536, some c535, some c354, some c75, some c129, some c537, some c287, some c215, some c39, some c19, some c170, some c199, some c7, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p538 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 31) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c491, c519, c530, c532, c212, c536, c535, c354, c75, c129, c537, c287, c215, c39, c19, c170, c199, c7] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c530 := derived530 a h
  have h3 : Entails.eval a c532 := derived532 a h
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c536 := derived536 a h
  have h6 : Entails.eval a c535 := derived535 a h
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c537 := derived537 a h
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c215 := h 214 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c170 := h 169 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c530, some c532, some c212, some c538, some c67, some c537, some c227, some c221, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p539 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 31) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c491, c530, c532, c212, c538, c67, c537, c227, c221] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c530 := derived530 a h
  have h2 : Entails.eval a c532 := derived532 a h
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c538 := derived538 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c537 := derived537 a h
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c282, some c539, some c65, some c54, some c67, some c212, some c227, some c299, some c126, some c344, some c339, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p540 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 31) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c491, c519, c282, c539, c65, c54, c67, c212, c227, c299, c126, c344, c339] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c282 := h 281 (by decide)
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c212 := h 211 (by decide)
  have h8 : Entails.eval a c227 := h 226 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  have h11 : Entails.eval a c344 := h 343 (by decide)
  have h12 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c282, some c539, some c65, some c54, some c354, some c540, some c50, some c314, some c163, some c124, some c378, some c281, some c28, some c366, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p541 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 31) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c491, c519, c282, c539, c65, c54, c354, c540, c50, c314, c163, c124, c378, c281, c28, c366] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c282 := h 281 (by decide)
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c540 := derived540 a h
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c314 := h 313 (by decide)
  have h10 : Entails.eval a c163 := h 162 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c378 := h 377 (by decide)
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c354, some c539, some c67, some c282, some c65, some c54, some c541, some c270, some c19, some c361, some c1, some c366, some c347, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p542 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 31) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c491, c519, c354, c539, c67, c282, c65, c54, c541, c270, c19, c361, c1, c366, c347] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c541 := derived541 a h
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨4, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c354, some c542, some c71, some c212, some c536, some c539, some c54, some c19, some c361, some c1, some c366, some c335, some c347, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p543 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 31) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c491, c519, c354, c542, c71, c212, c536, c539, c54, c19, c361, c1, c366, c335, c347] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c542 := derived542 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c536 := derived536 a h
  have h7 : Entails.eval a c539 := derived539 a h
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c366 := h 365 (by decide)
  have h13 : Entails.eval a c335 := h 334 (by decide)
  have h14 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c463, some c382, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p544 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 31) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c463, c382] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c463 := derived463 a h
  have h1 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c545 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c539, some c519, some c354, some c542, some c71, some c212, some c536, some c544, some c54, some c543, some c187, some c299, some c39, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p545 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 31) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c491, c539, c519, c354, c542, c71, c212, c536, c544, c54, c543, c187, c299, c39] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c539 := derived539 a h
  have h2 : Entails.eval a c519 := derived519 a h
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c542 := derived542 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c536 := derived536 a h
  have h8 : Entails.eval a c544 := derived544 a h
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c543 := derived543 a h
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨20, by decide⟩, false), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c71, some c187, some c380, some c39, some c338, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p546 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 31) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c71, c187, c380, c39, c338] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨20, by decide⟩, false), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c545, some c539, some c519, some c73, some c59, some c54, some c546, some c286, some c378, some c160, some c26, some c20, some c16, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p547 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 31) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c545, c539, c519, c73, c59, c54, c546, c286, c378, c160, c26, c20, c16] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c545 := derived545 a h
  have h1 : Entails.eval a c539 := derived539 a h
  have h2 : Entails.eval a c519 := derived519 a h
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c546 := derived546 a h
  have h7 : Entails.eval a c286 := h 285 (by decide)
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c545, some c519, some c547, some c282, some c527, some c380, some c515, some c466, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p548 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 31) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c491, c545, c519, c547, c282, c527, c380, c515, c466] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c519 := derived519 a h
  have h3 : Entails.eval a c547 := derived547 a h
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c527 := derived527 a h
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c515 := derived515 a h
  have h8 : Entails.eval a c466 := derived466 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c545, some c539, some c519, some c548, some c377, some c311, some c73, some c59, some c54, some c315, some c214, some c515, some c289, some c331, some c44, some c325, some c402, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p549 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 31) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c491, c545, c539, c519, c548, c377, c311, c73, c59, c54, c315, c214, c515, c289, c331, c44, c325, c402] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c539 := derived539 a h
  have h3 : Entails.eval a c519 := derived519 a h
  have h4 : Entails.eval a c548 := derived548 a h
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c214 := h 213 (by decide)
  have h12 : Entails.eval a c515 := derived515 a h
  have h13 : Entails.eval a c289 := h 288 (by decide)
  have h14 : Entails.eval a c331 := h 330 (by decide)
  have h15 : Entails.eval a c44 := h 43 (by decide)
  have h16 : Entails.eval a c325 := h 324 (by decide)
  have h17 : Entails.eval a c402 := h 401 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c545, some c519, some c377, some c64, some c311, some c73, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p550 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 31) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c545, c519, c377, c64, c311, c73] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c545 := derived545 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨20, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c539, some c545, some c59, some c50, some c128, some c97, some c495, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p551 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 31) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c539, c545, c59, c50, c128, c97, c495] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c539 := derived539 a h
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c128 := h 127 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c495 := derived495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c550, some c545, some c73, some c551, some c515, some c316, some c214, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p552 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 31) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c550, c545, c73, c551, c515, c316, c214] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c550 := derived550 a h
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c551 := derived551 a h
  have h4 : Entails.eval a c515 := derived515 a h
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c545, some c539, some c519, some c549, some c550, some c552, some c282, some c527, some c210, some c187, some c515, some c466, some c18, some c26, some c501, some c107, some c387, some c195, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p553 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 31) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c491, c545, c539, c519, c549, c550, c552, c282, c527, c210, c187, c515, c466, c18, c26, c501, c107, c387, c195] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c539 := derived539 a h
  have h3 : Entails.eval a c519 := derived519 a h
  have h4 : Entails.eval a c549 := derived549 a h
  have h5 : Entails.eval a c550 := derived550 a h
  have h6 : Entails.eval a c552 := derived552 a h
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c527 := derived527 a h
  have h9 : Entails.eval a c210 := h 209 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c515 := derived515 a h
  have h12 : Entails.eval a c466 := derived466 a h
  have h13 : Entails.eval a c18 := h 17 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c501 := derived501 a h
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c387 := h 386 (by decide)
  have h18 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c545, some c552, some c527, some c282, some c210, some c316, some c553, some c539, some c501, some c497, some c387, some c2, some c41, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p554 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 31) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c491, c519, c545, c552, c527, c282, c210, c316, c553, c539, c501, c497, c387, c2, c41] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c545 := derived545 a h
  have h3 : Entails.eval a c552 := derived552 a h
  have h4 : Entails.eval a c527 := derived527 a h
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c553 := derived553 a h
  have h9 : Entails.eval a c539 := derived539 a h
  have h10 : Entails.eval a c501 := derived501 a h
  have h11 : Entails.eval a c497 := derived497 a h
  have h12 : Entails.eval a c387 := h 386 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c553, some c545, some c519, some c550, some c552, some c282, some c527, some c210, some c316, some c554, some c22, some c152, some c513, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p555 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 31) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c491, c553, c545, c519, c550, c552, c282, c527, c210, c316, c554, c22, c152, c513] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c553 := derived553 a h
  have h2 : Entails.eval a c545 := derived545 a h
  have h3 : Entails.eval a c519 := derived519 a h
  have h4 : Entails.eval a c550 := derived550 a h
  have h5 : Entails.eval a c552 := derived552 a h
  have h6 : Entails.eval a c282 := h 281 (by decide)
  have h7 : Entails.eval a c527 := derived527 a h
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c554 := derived554 a h
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c513 := derived513 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c553, some c545, some c539, some c519, some c25, some c29, some c102, some c527, some c513, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p556 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 31) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c553, c545, c539, c519, c25, c29, c102, c527, c513] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c553 := derived553 a h
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c539 := derived539 a h
  have h3 : Entails.eval a c519 := derived519 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c527 := derived527 a h
  have h8 : Entails.eval a c513 := derived513 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c519, some c539, some c545, some c553, some c555, some c556, some c501, some c497, some c97, some c12, some c2, some c282, some c527, some c210, some c107, some c176, some c515, some c247, some c143, some c371, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p557 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 31) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c491, c519, c539, c545, c553, c555, c556, c501, c497, c97, c12, c2, c282, c527, c210, c107, c176, c515, c247, c143, c371] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c539 := derived539 a h
  have h3 : Entails.eval a c545 := derived545 a h
  have h4 : Entails.eval a c553 := derived553 a h
  have h5 : Entails.eval a c555 := derived555 a h
  have h6 : Entails.eval a c556 := derived556 a h
  have h7 : Entails.eval a c501 := derived501 a h
  have h8 : Entails.eval a c497 := derived497 a h
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c282 := h 281 (by decide)
  have h13 : Entails.eval a c527 := derived527 a h
  have h14 : Entails.eval a c210 := h 209 (by decide)
  have h15 : Entails.eval a c107 := h 106 (by decide)
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c515 := derived515 a h
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c143 := h 142 (by decide)
  have h20 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c557, some c497, some c2, some c97, some c527, some c536, some c515, some c466, some c247, some c351, some c401, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p558 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 31) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c491, c557, c497, c2, c97, c527, c536, c515, c466, c247, c351, c401] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c527 := derived527 a h
  have h6 : Entails.eval a c536 := derived536 a h
  have h7 : Entails.eval a c515 := derived515 a h
  have h8 : Entails.eval a c466 := derived466 a h
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c401 := h 400 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, false), (⟨14, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c97, some c515, some c466, some c362, some c60, some c3, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p559 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 31) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c557, c97, c515, c466, c362, c60, c3] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c515 := derived515 a h
  have h3 : Entails.eval a c466 := derived466 a h
  have h4 : Entails.eval a c362 := h 361 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨14, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c559, some c97, some c70, some c362, some c247, some c186, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p560 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 31) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c491, c559, c97, c70, c362, c247, c186] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c362 := h 361 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  have h6 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c497, some c97, some c2, some c558, some c559, some c127, some c191, some c560, some c211, some c255, some c327, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p561 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 31) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c491, c497, c97, c2, c558, c559, c127, c191, c560, c211, c255, c327] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c558 := derived558 a h
  have h5 : Entails.eval a c559 := derived559 a h
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c560 := derived560 a h
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c255 := h 254 (by decide)
  have h11 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c557, some c60, some c3, some c292, some c128, some c393, some c392, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p562 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 31) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c491, c557, c60, c3, c292, c128, c393, c392] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c128 := h 127 (by decide)
  have h6 : Entails.eval a c393 := h 392 (by decide)
  have h7 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c562, some c312, some c425, some c379, some c247, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p563 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 31) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c491, c562, c312, c425, c379, c247] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c562 := derived562 a h
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c425 := derived425 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c491, some c563, some c515, some c466, some c70, some c356, some c60, some c247, some c316, some c292, some c380, some c388, some c395, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p564 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 31) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c557, c491, c563, c515, c466, c70, c356, c60, c247, c316, c292, c380, c388, c395] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c563 := derived563 a h
  have h3 : Entails.eval a c515 := derived515 a h
  have h4 : Entails.eval a c466 := derived466 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c292 := h 291 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c388 := h 387 (by decide)
  have h13 : Entails.eval a c395 := h 394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c561, some c497, some c166, some c103, some c170, some c3, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p565 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 31) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c561, c497, c166, c103, c170, c3] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c491, some c497, some c561, some c501, some c565, some c564, some c282, some c527, some c536, some c515, some c466, some c247, some c60, some c51, some c3, some c138, some c229, some c144, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p566 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 31) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c557, c491, c497, c561, c501, c565, c564, c282, c527, c536, c515, c466, c247, c60, c51, c3, c138, c229, c144] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c561 := derived561 a h
  have h4 : Entails.eval a c501 := derived501 a h
  have h5 : Entails.eval a c565 := derived565 a h
  have h6 : Entails.eval a c564 := derived564 a h
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c527 := derived527 a h
  have h9 : Entails.eval a c536 := derived536 a h
  have h10 : Entails.eval a c515 := derived515 a h
  have h11 : Entails.eval a c466 := derived466 a h
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c138 := h 137 (by decide)
  have h17 : Entails.eval a c229 := h 228 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c491, some c566, some c29, some c25, some c527, some c536, some c515, some c466, some c247, some c26, some c60, some c153, some c118, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p567 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 31) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c557, c491, c566, c29, c25, c527, c536, c515, c466, c247, c26, c60, c153, c118] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c566 := derived566 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c527 := derived527 a h
  have h6 : Entails.eval a c536 := derived536 a h
  have h7 : Entails.eval a c515 := derived515 a h
  have h8 : Entails.eval a c466 := derived466 a h
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c491, some c567, some c566, some c29, some c25, some c515, some c466, some c70, some c26, some c240, some c118, some c276, some c136, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p568 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 31) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c557, c491, c567, c566, c29, c25, c515, c466, c70, c26, c240, c118, c276, c136] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c566 := derived566 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c515 := derived515 a h
  have h7 : Entails.eval a c466 := derived466 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c240 := h 239 (by decide)
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true), (⟨19, by decide⟩, false), (⟨2, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c557, some c118, some c151, some c62, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p569 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 31) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c491, c557, c118, c151, c62] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c151 := h 150 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c567, some c566, some c29, some c25, some c568, some c569, some c26, some c312, some c425, some c379, some c247, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p570 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 31) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c491, c567, c566, c29, c25, c568, c569, c26, c312, c425, c379, c247] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c567 := derived567 a h
  have h2 : Entails.eval a c566 := derived566 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c568 := derived568 a h
  have h6 : Entails.eval a c569 := derived569 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c312 := h 311 (by decide)
  have h9 : Entails.eval a c425 := derived425 a h
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c570, some c60, some c567, some c566, some c29, some c504, some c312, some c127, some c457, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p571 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 31) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c557, c570, c60, c567, c566, c29, c504, c312, c127, c457] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c570 := derived570 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c567 := derived567 a h
  have h4 : Entails.eval a c566 := derived566 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c504 := derived504 a h
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c457 := derived457 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c25, some c570, some c60, some c571, some c515, some c466, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p572 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 31) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c557, c25, c570, c60, c571, c515, c466] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c570 := derived570 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c571 := derived571 a h
  have h5 : Entails.eval a c515 := derived515 a h
  have h6 : Entails.eval a c466 := derived466 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c566, some c572, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p573 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 31) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c566, c572] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c566 := derived566 a h
  have h1 : Entails.eval a c572 := derived572 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c574 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨15, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c60, some c573, some c515, some c135, some c466, some c59, some c97, some c4, some c179, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p574 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 31) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c557, c60, c573, c515, c135, c466, c59, c97, c4, c179] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c573 := derived573 a h
  have h3 : Entails.eval a c515 := derived515 a h
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c466 := derived466 a h
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c573, some c59, some c97, some c4, some c80, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p575 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 31) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c573, c59, c97, c4, c80] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c491, some c60, some c574, some c495, some c575, some c527, some c425, some c312, some c247, some c379, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p576 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 31) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c557, c491, c60, c574, c495, c575, c527, c425, c312, c247, c379] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c574 := derived574 a h
  have h4 : Entails.eval a c495 := derived495 a h
  have h5 : Entails.eval a c575 := derived575 a h
  have h6 : Entails.eval a c527 := derived527 a h
  have h7 : Entails.eval a c425 := derived425 a h
  have h8 : Entails.eval a c312 := h 311 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c495, some c576, some c527, some c569, some c26, some c425, some c312, some c247, some c379, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p577 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 31) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c491, c495, c576, c527, c569, c26, c425, c312, c247, c379] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c495 := derived495 a h
  have h2 : Entails.eval a c576 := derived576 a h
  have h3 : Entails.eval a c527 := derived527 a h
  have h4 : Entails.eval a c569 := derived569 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c425 := derived425 a h
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c573, some c495, some c577, some c97, some c166, some c102, some c169, some c4, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p578 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 31) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c573, c495, c577, c97, c166, c102, c169, c4] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c495 := derived495 a h
  have h2 : Entails.eval a c577 := derived577 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c169 := h 168 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c578, some c515, some c573, some c73, some c284, some c214, some c524, some c18, some c316, some c26, some c378, some c129, some c546, some c155, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p579 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 31) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c578, c515, c573, c73, c284, c214, c524, c18, c316, c26, c378, c129, c546, c155] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c578 := derived578 a h
  have h1 : Entails.eval a c515 := derived515 a h
  have h2 : Entails.eval a c573 := derived573 a h
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c214 := h 213 (by decide)
  have h6 : Entails.eval a c524 := derived524 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  have h12 : Entails.eval a c546 := derived546 a h
  have h13 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c573, some c578, some c515, some c579, some c466, some c26, some c18, some c70, some c536, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p580 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 31) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c573, c578, c515, c579, c466, c26, c18, c70, c536] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c578 := derived578 a h
  have h2 : Entails.eval a c515 := derived515 a h
  have h3 : Entails.eval a c579 := derived579 a h
  have h4 : Entails.eval a c466 := derived466 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c536 := derived536 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c557, some c515, some c580, some c573, some c466, some c60, some c3, some c228, some c45, some c192, some c13, some c174, some c112, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p581 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 31) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c491, c557, c515, c580, c573, c466, c60, c3, c228, c45, c192, c13, c174, c112] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c515 := derived515 a h
  have h3 : Entails.eval a c580 := derived580 a h
  have h4 : Entails.eval a c573 := derived573 a h
  have h5 : Entails.eval a c466 := derived466 a h
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c174 := h 173 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c515, some c581, some c284, some c73, some c214, some c524, some c580, some c573, some c60, some c254, some c3, some c44, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p582 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 31) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c557, c515, c581, c284, c73, c214, c524, c580, c573, c60, c254, c3, c44] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c515 := derived515 a h
  have h2 : Entails.eval a c581 := derived581 a h
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c214 := h 213 (by decide)
  have h6 : Entails.eval a c524 := derived524 a h
  have h7 : Entails.eval a c580 := derived580 a h
  have h8 : Entails.eval a c573 := derived573 a h
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c254 := h 253 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c573, some c515, some c581, some c73, some c284, some c214, some c524, some c316, some c582, some c378, some c129, some c546, some c54, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p583 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 31) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c573, c515, c581, c73, c284, c214, c524, c316, c582, c378, c129, c546, c54] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c515 := derived515 a h
  have h2 : Entails.eval a c581 := derived581 a h
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c214 := h 213 (by decide)
  have h6 : Entails.eval a c524 := derived524 a h
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c582 := derived582 a h
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c129 := h 128 (by decide)
  have h11 : Entails.eval a c546 := derived546 a h
  have h12 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨28, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c557, some c73, some c583, some c580, some c573, some c312, some c378, some c71, some c66, some c52, some c214, some c3, some c44, some c289, some c321, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p584 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 31) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c491, c557, c73, c583, c580, c573, c312, c378, c71, c66, c52, c214, c3, c44, c289, c321] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c583 := derived583 a h
  have h4 : Entails.eval a c580 := derived580 a h
  have h5 : Entails.eval a c573 := derived573 a h
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c214 := h 213 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  have h14 : Entails.eval a c289 := h 288 (by decide)
  have h15 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c491, some c583, some c580, some c584, some c60, some c3, some c128, some c44, some c45, some c377, some c220, some c284, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p585 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 31) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c557, c491, c583, c580, c584, c60, c3, c128, c44, c45, c377, c220, c284] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c583 := derived583 a h
  have h3 : Entails.eval a c580 := derived580 a h
  have h4 : Entails.eval a c584 := derived584 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c220 := h 219 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c491, some c583, some c585, some c527, some c580, some c60, some c3, some c128, some c292, some c45, some c247, some c70, some c210, some c220, some c363, some c191, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p586 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 31) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c557, c491, c583, c585, c527, c580, c60, c3, c128, c292, c45, c247, c70, c210, c220, c363, c191] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c583 := derived583 a h
  have h3 : Entails.eval a c585 := derived585 a h
  have h4 : Entails.eval a c527 := derived527 a h
  have h5 : Entails.eval a c580 := derived580 a h
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c128 := h 127 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c527, some c586, some c425, some c312, some c247, some c379, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p587 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 31) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c491, c527, c586, c425, c312, c247, c379] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c527 := derived527 a h
  have h2 : Entails.eval a c586 := derived586 a h
  have h3 : Entails.eval a c425 := derived425 a h
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c583, some c585, some c587, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p588 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 31) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c583, c585, c587] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c585 := derived585 a h
  have h2 : Entails.eval a c587 := derived587 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c557, some c588, some c283, some c354, some c71, some c65, some c314, some c378, some c282, some c128, some c16, some c113, some c19, some c101, some c122, some c310, some c15, some c308, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p589 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 31) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c491, c557, c588, c283, c354, c71, c65, c314, c378, c282, c128, c16, c113, c19, c101, c122, c310, c15, c308] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c588 := derived588 a h
  have h3 : Entails.eval a c283 := h 282 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c282 := h 281 (by decide)
  have h10 : Entails.eval a c128 := h 127 (by decide)
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c122 := h 121 (by decide)
  have h16 : Entails.eval a c310 := h 309 (by decide)
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c588, some c491, some c557, some c589, some c495, some c283, some c354, some c71, some c282, some c67, some c65, some c314, some c378, some c251, some c39, some c87, some c256, some c203, some c404, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p590 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 31) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c588, c491, c557, c589, c495, c283, c354, c71, c282, c67, c65, c314, c378, c251, c39, c87, c256, c203, c404] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c588 := derived588 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c557 := derived557 a h
  have h3 : Entails.eval a c589 := derived589 a h
  have h4 : Entails.eval a c495 := derived495 a h
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c378 := h 377 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c87 := h 86 (by decide)
  have h16 : Entails.eval a c256 := h 255 (by decide)
  have h17 : Entails.eval a c203 := h 202 (by decide)
  have h18 : Entails.eval a c404 := h 403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c588, some c491, some c557, some c283, some c354, some c71, some c65, some c314, some c378, some c391, some c397, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p591 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 31) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c588, c491, c557, c283, c354, c71, c65, c314, c378, c391, c397] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c588 := derived588 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c557 := derived557 a h
  have h3 : Entails.eval a c283 := h 282 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c391 := h 390 (by decide)
  have h10 : Entails.eval a c397 := h 396 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c557, some c588, some c589, some c495, some c283, some c354, some c71, some c65, some c282, some c590, some c591, some c7, some c385, some c19, some c146, some c310, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p592 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 31) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c491, c557, c588, c589, c495, c283, c354, c71, c65, c282, c590, c591, c7, c385, c19, c146, c310] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c588 := derived588 a h
  have h3 : Entails.eval a c589 := derived589 a h
  have h4 : Entails.eval a c495 := derived495 a h
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c282 := h 281 (by decide)
  have h10 : Entails.eval a c590 := derived590 a h
  have h11 : Entails.eval a c591 := derived591 a h
  have h12 : Entails.eval a c7 := h 6 (by decide)
  have h13 : Entails.eval a c385 := h 384 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c588, some c491, some c557, some c592, some c283, some c354, some c71, some c282, some c67, some c65, some c314, some c378, some c251, some c19, some c101, some c218, some c302, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p593 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 31) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c588, c491, c557, c592, c283, c354, c71, c282, c67, c65, c314, c378, c251, c19, c101, c218, c302] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c588 := derived588 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c557 := derived557 a h
  have h3 : Entails.eval a c592 := derived592 a h
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c314 := h 313 (by decide)
  have h11 : Entails.eval a c378 := h 377 (by decide)
  have h12 : Entails.eval a c251 := h 250 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c218 := h 217 (by decide)
  have h16 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c557, some c588, some c283, some c354, some c71, some c67, some c282, some c65, some c314, some c378, some c251, some c589, some c495, some c592, some c593, some c132, some c298, some c348, some c374, some c119, some c242, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p594 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 31) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c491, c557, c588, c283, c354, c71, c67, c282, c65, c314, c378, c251, c589, c495, c592, c593, c132, c298, c348, c374, c119, c242] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c588 := derived588 a h
  have h3 : Entails.eval a c283 := h 282 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c314 := h 313 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c589 := derived589 a h
  have h13 : Entails.eval a c495 := derived495 a h
  have h14 : Entails.eval a c592 := derived592 a h
  have h15 : Entails.eval a c593 := derived593 a h
  have h16 : Entails.eval a c132 := h 131 (by decide)
  have h17 : Entails.eval a c298 := h 297 (by decide)
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c119 := h 118 (by decide)
  have h21 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c594, some c588, some c491, some c212, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p595 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 31) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c594, c588, c491, c212] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c594 := derived594 a h
  have h1 : Entails.eval a c588 := derived588 a h
  have h2 : Entails.eval a c491 := derived491 a h
  have h3 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c588, some c557, some c29, some c116, some c11, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p596 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 31) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c491, c588, c557, c29, c116, c11] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c588 := derived588 a h
  have h2 : Entails.eval a c557 := derived557 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨25, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c595, some c235, some c326, some c271, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p597 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 31) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c595, c235, c326, c271] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c595 := derived595 a h
  have h1 : Entails.eval a c235 := h 234 (by decide)
  have h2 : Entails.eval a c326 := h 325 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c595, some c491, some c588, some c596, some c597, some c350, some c173, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p598 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 31) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c557, c595, c491, c588, c596, c597, c350, c173] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c491 := derived491 a h
  have h3 : Entails.eval a c588 := derived588 a h
  have h4 : Entails.eval a c596 := derived596 a h
  have h5 : Entails.eval a c597 := derived597 a h
  have h6 : Entails.eval a c350 := h 349 (by decide)
  have h7 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c491, some c594, some c595, some c536, some c69, some c70, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p599 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 31) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c491, c594, c595, c536, c69, c70] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c595 := derived595 a h
  have h3 : Entails.eval a c536 := derived536 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c599, some c595, some c594, some c588, some c557, some c596, some c598, some c384, some c287, some c170, some c234, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p600 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 31) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c599, c595, c594, c588, c557, c596, c598, c384, c287, c170, c234] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c599 := derived599 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c594 := derived594 a h
  have h3 : Entails.eval a c588 := derived588 a h
  have h4 : Entails.eval a c557 := derived557 a h
  have h5 : Entails.eval a c596 := derived596 a h
  have h6 : Entails.eval a c598 := derived598 a h
  have h7 : Entails.eval a c384 := h 383 (by decide)
  have h8 : Entails.eval a c287 := h 286 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c599, some c595, some c179, some c278, some c244, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p601 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 31) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c557, c599, c595, c179, c278, c244] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c599 := derived599 a h
  have h2 : Entails.eval a c595 := derived595 a h
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c278 := h 277 (by decide)
  have h5 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c595, some c557, some c599, some c350, some c601, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p602 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 31) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c595, c557, c599, c350, c601] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c595 := derived595 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c599 := derived599 a h
  have h3 : Entails.eval a c350 := h 349 (by decide)
  have h4 : Entails.eval a c601 := derived601 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c595, some c588, some c491, some c600, some c217, some c602, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p603 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 31) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c557, c595, c588, c491, c600, c217, c602] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c588 := derived588 a h
  have h3 : Entails.eval a c491 := derived491 a h
  have h4 : Entails.eval a c600 := derived600 a h
  have h5 : Entails.eval a c217 := h 216 (by decide)
  have h6 : Entails.eval a c602 := derived602 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c599, some c595, some c295, some c225, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p604 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 31) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c599, c595, c295, c225] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c599 := derived599 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived604

end CochromaticTwenty.Certificates.Z12Direct_5_3_13
