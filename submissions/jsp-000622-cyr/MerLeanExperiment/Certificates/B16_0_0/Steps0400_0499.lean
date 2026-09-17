import MerLeanExperiment.Certificates.B16_0_0.Steps0300_0399

/-! Generated from the actual pinned b16_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c794 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, false), (⟨3, by decide⟩, true), (⟨43, by decide⟩, false), (⟨16, by decide⟩, false), (⟨18, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c132, some c200, some c128, some c266, some c237, some c206, some c3, some c22, some c269, some c152, some c161, some c218, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 57) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c376, c132, c200, c128, c266, c237, c206, c3, c22, c269, c152, c161, c218] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c237 := h 236 (by decide)
  have h6 : Entails.eval a c206 := h 205 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c269 := h 268 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c789, some c788, some c782, some c257, some c393, some c387, some c778, some c428, some c645, some c310, some c787, some c790, some c376, some c84, some c363, some c791, some c191, some c793, some c50, some c794, some c316, some c133, some c235, some c233, some c211, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 57) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c789, c788, c782, c257, c393, c387, c778, c428, c645, c310, c787, c790, c376, c84, c363, c791, c191, c793, c50, c794, c316, c133, c235, c233, c211] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c789 := derived789 a h
  have h1 : Entails.eval a c788 := derived788 a h
  have h2 : Entails.eval a c782 := derived782 a h
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c393 := h 392 (by decide)
  have h5 : Entails.eval a c387 := h 386 (by decide)
  have h6 : Entails.eval a c778 := derived778 a h
  have h7 : Entails.eval a c428 := derived428 a h
  have h8 : Entails.eval a c645 := derived645 a h
  have h9 : Entails.eval a c310 := h 309 (by decide)
  have h10 : Entails.eval a c787 := derived787 a h
  have h11 : Entails.eval a c790 := derived790 a h
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c84 := h 83 (by decide)
  have h14 : Entails.eval a c363 := h 362 (by decide)
  have h15 : Entails.eval a c791 := derived791 a h
  have h16 : Entails.eval a c191 := h 190 (by decide)
  have h17 : Entails.eval a c793 := derived793 a h
  have h18 : Entails.eval a c50 := h 49 (by decide)
  have h19 : Entails.eval a c794 := derived794 a h
  have h20 : Entails.eval a c316 := h 315 (by decide)
  have h21 : Entails.eval a c133 := h 132 (by decide)
  have h22 : Entails.eval a c235 := h 234 (by decide)
  have h23 : Entails.eval a c233 := h 232 (by decide)
  have h24 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c393, some c778, some c792, some c428, some c757, some c645, some c789, some c795, some c135, some c293, some c191, some c84, some c15, some c12, some c201, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 57) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c387, c393, c778, c792, c428, c757, c645, c789, c795, c135, c293, c191, c84, c15, c12, c201] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c792 := derived792 a h
  have h4 : Entails.eval a c428 := derived428 a h
  have h5 : Entails.eval a c757 := derived757 a h
  have h6 : Entails.eval a c645 := derived645 a h
  have h7 : Entails.eval a c789 := derived789 a h
  have h8 : Entails.eval a c795 := derived795 a h
  have h9 : Entails.eval a c135 := h 134 (by decide)
  have h10 : Entails.eval a c293 := h 292 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨27, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c796, some c387, some c393, some c778, some c792, some c94, some c428, some c757, some c187, some c2, some c12, some c11, some c191, some c200, some c204, some c135, some c134, some c607, some c306, some c133, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 57) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c493, c796, c387, c393, c778, c792, c94, c428, c757, c187, c2, c12, c11, c191, c200, c204, c135, c134, c607, c306, c133] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c387 := h 386 (by decide)
  have h3 : Entails.eval a c393 := h 392 (by decide)
  have h4 : Entails.eval a c778 := derived778 a h
  have h5 : Entails.eval a c792 := derived792 a h
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c428 := derived428 a h
  have h8 : Entails.eval a c757 := derived757 a h
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c200 := h 199 (by decide)
  have h15 : Entails.eval a c204 := h 203 (by decide)
  have h16 : Entails.eval a c135 := h 134 (by decide)
  have h17 : Entails.eval a c134 := h 133 (by decide)
  have h18 : Entails.eval a c607 := derived607 a h
  have h19 : Entails.eval a c306 := h 305 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c387, some c757, some c645, some c493, some c778, some c428, some c792, some c796, some c94, some c61, some c101, some c389, some c797, some c587, some c606, some c191, some c382, some c341, some c135, some c368, some c310, some c89, some c295, some c74, some c340, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 57) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c393, c387, c757, c645, c493, c778, c428, c792, c796, c94, c61, c101, c389, c797, c587, c606, c191, c382, c341, c135, c368, c310, c89, c295, c74, c340] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c493 := derived493 a h
  have h5 : Entails.eval a c778 := derived778 a h
  have h6 : Entails.eval a c428 := derived428 a h
  have h7 : Entails.eval a c792 := derived792 a h
  have h8 : Entails.eval a c796 := derived796 a h
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c101 := h 100 (by decide)
  have h12 : Entails.eval a c389 := h 388 (by decide)
  have h13 : Entails.eval a c797 := derived797 a h
  have h14 : Entails.eval a c587 := derived587 a h
  have h15 : Entails.eval a c606 := derived606 a h
  have h16 : Entails.eval a c191 := h 190 (by decide)
  have h17 : Entails.eval a c382 := h 381 (by decide)
  have h18 : Entails.eval a c341 := h 340 (by decide)
  have h19 : Entails.eval a c135 := h 134 (by decide)
  have h20 : Entails.eval a c368 := h 367 (by decide)
  have h21 : Entails.eval a c310 := h 309 (by decide)
  have h22 : Entails.eval a c89 := h 88 (by decide)
  have h23 : Entails.eval a c295 := h 294 (by decide)
  have h24 : Entails.eval a c74 := h 73 (by decide)
  have h25 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨48, by decide⟩, false), (⟨16, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c101, some c645, some c382, some c94, some c389, some c368, some c89, some c8, some c244, some c541, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c493, c101, c645, c382, c94, c389, c368, c89, c8, c244, c541] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c389 := h 388 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c541 := derived541 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨48, by decide⟩, false), (⟨16, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c101, some c799, some c109, some c110, some c17, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c493, c101, c799, c109, c110, c17] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c799 := derived799 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨34, by decide⟩, false), (⟨22, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨11, by decide⟩, false), (⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c208, some c156, some c48, some c743, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c2, c208, c156, c48, c743] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c743 := derived743 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c798, some c393, some c387, some c757, some c645, some c587, some c606, some c191, some c382, some c172, some c800, some c91, some c775, some c8, some c792, some c742, some c244, some c475, some c801, some c236, some c133, some c196, some c156, some c10, some c743, some c105, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c798, c393, c387, c757, c645, c587, c606, c191, c382, c172, c800, c91, c775, c8, c792, c742, c244, c475, c801, c236, c133, c196, c156, c10, c743, c105] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c798 := derived798 a h
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c387 := h 386 (by decide)
  have h3 : Entails.eval a c757 := derived757 a h
  have h4 : Entails.eval a c645 := derived645 a h
  have h5 : Entails.eval a c587 := derived587 a h
  have h6 : Entails.eval a c606 := derived606 a h
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c800 := derived800 a h
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c775 := derived775 a h
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c792 := derived792 a h
  have h15 : Entails.eval a c742 := derived742 a h
  have h16 : Entails.eval a c244 := h 243 (by decide)
  have h17 : Entails.eval a c475 := derived475 a h
  have h18 : Entails.eval a c801 := derived801 a h
  have h19 : Entails.eval a c236 := h 235 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c196 := h 195 (by decide)
  have h22 : Entails.eval a c156 := h 155 (by decide)
  have h23 : Entails.eval a c10 := h 9 (by decide)
  have h24 : Entails.eval a c743 := derived743 a h
  have h25 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c91, some c382, some c802, some c798, some c393, some c757, some c135, some c172, some c201, some c204, some c189, some c368, some c381, some c133, some c306, some c57, some c277, some c58, some c347, some c48, some c339, some c118, some c27, some c244, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c645, c91, c382, c802, c798, c393, c757, c135, c172, c201, c204, c189, c368, c381, c133, c306, c57, c277, c58, c347, c48, c339, c118, c27, c244] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c802 := derived802 a h
  have h4 : Entails.eval a c798 := derived798 a h
  have h5 : Entails.eval a c393 := h 392 (by decide)
  have h6 : Entails.eval a c757 := derived757 a h
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c381 := h 380 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c306 := h 305 (by decide)
  have h16 : Entails.eval a c57 := h 56 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c58 := h 57 (by decide)
  have h19 : Entails.eval a c347 := h 346 (by decide)
  have h20 : Entails.eval a c48 := h 47 (by decide)
  have h21 : Entails.eval a c339 := h 338 (by decide)
  have h22 : Entails.eval a c118 := h 117 (by decide)
  have h23 : Entails.eval a c27 := h 26 (by decide)
  have h24 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c382, some c493, some c341, some c351, some c339, some c360, some c368, some c57, some c389, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c645, c382, c493, c341, c351, c339, c360, c368, c57, c389] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c341 := h 340 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c339 := h 338 (by decide)
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c253, some c187, some c2, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c253, c187, c2] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c12, some c267, some c107, some c600, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c2, c12, c267, c107, c600] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c600 := derived600 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c393, some c645, some c382, some c91, some c803, some c191, some c804, some c27, some c244, some c475, some c806, some c201, some c157, some c174, some c72, some c90, some c505, some c74, some c340, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c802, c393, c645, c382, c91, c803, c191, c804, c27, c244, c475, c806, c201, c157, c174, c72, c90, c505, c74, c340] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c803 := derived803 a h
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c804 := derived804 a h
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c475 := derived475 a h
  have h11 : Entails.eval a c806 := derived806 a h
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c157 := h 156 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c90 := h 89 (by decide)
  have h17 : Entails.eval a c505 := derived505 a h
  have h18 : Entails.eval a c74 := h 73 (by decide)
  have h19 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨40, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c201, some c393, some c387, some c191, some c197, some c157, some c612, some c1, some c72, some c56, some c428, some c74, some c7, some c357, some c266, some c505, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c802, c201, c393, c387, c191, c197, c157, c612, c1, c72, c56, c428, c74, c7, c357, c266, c505] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c612 := derived612 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c428 := derived428 a h
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c7 := h 6 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c505 := derived505 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨40, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c475, some c802, some c798, some c393, some c387, some c757, some c645, some c203, some c201, some c808, some c135, some c172, some c310, some c376, some c84, some c363, some c13, some c502, some c3, some c14, some c428, some c50, some c277, some c330, some c267, some c31, some c117, some c292, some c241, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c475, c802, c798, c393, c387, c757, c645, c203, c201, c808, c135, c172, c310, c376, c84, c363, c13, c502, c3, c14, c428, c50, c277, c330, c267, c31, c117, c292, c241] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c798 := derived798 a h
  have h3 : Entails.eval a c393 := h 392 (by decide)
  have h4 : Entails.eval a c387 := h 386 (by decide)
  have h5 : Entails.eval a c757 := derived757 a h
  have h6 : Entails.eval a c645 := derived645 a h
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c808 := derived808 a h
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c310 := h 309 (by decide)
  have h13 : Entails.eval a c376 := h 375 (by decide)
  have h14 : Entails.eval a c84 := h 83 (by decide)
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c502 := derived502 a h
  have h18 : Entails.eval a c3 := h 2 (by decide)
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c428 := derived428 a h
  have h21 : Entails.eval a c50 := h 49 (by decide)
  have h22 : Entails.eval a c277 := h 276 (by decide)
  have h23 : Entails.eval a c330 := h 329 (by decide)
  have h24 : Entails.eval a c267 := h 266 (by decide)
  have h25 : Entails.eval a c31 := h 30 (by decide)
  have h26 : Entails.eval a c117 := h 116 (by decide)
  have h27 : Entails.eval a c292 := h 291 (by decide)
  have h28 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c172, some c84, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c3, c172, c84] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨34, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c502, some c277, some c330, some c133, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c84, c502, c277, c330, c133] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c502 := derived502 a h
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c330 := h 329 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨45, by decide⟩, false), (⟨10, by decide⟩, true), (⟨34, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c277, some c353, some c133, some c342, some c332, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c277, c353, c133, c342, c332] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c277 := h 276 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c342 := h 341 (by decide)
  have h4 : Entails.eval a c332 := h 331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c475, some c802, some c798, some c393, some c387, some c757, some c645, some c2, some c806, some c267, some c191, some c810, some c189, some c811, some c368, some c812, some c58, some c568, some c105, some c257, some c263, some c56, some c1, some c155, some c223, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c475, c802, c798, c393, c387, c757, c645, c2, c806, c267, c191, c810, c189, c811, c368, c812, c58, c568, c105, c257, c263, c56, c1, c155, c223] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c798 := derived798 a h
  have h3 : Entails.eval a c393 := h 392 (by decide)
  have h4 : Entails.eval a c387 := h 386 (by decide)
  have h5 : Entails.eval a c757 := derived757 a h
  have h6 : Entails.eval a c645 := derived645 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c806 := derived806 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c810 := derived810 a h
  have h12 : Entails.eval a c189 := h 188 (by decide)
  have h13 : Entails.eval a c811 := derived811 a h
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c812 := derived812 a h
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c568 := derived568 a h
  have h18 : Entails.eval a c105 := h 104 (by decide)
  have h19 : Entails.eval a c257 := h 256 (by decide)
  have h20 : Entails.eval a c263 := h 262 (by decide)
  have h21 : Entails.eval a c56 := h 55 (by decide)
  have h22 : Entails.eval a c1 := h 0 (by decide)
  have h23 : Entails.eval a c155 := h 154 (by decide)
  have h24 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c475, some c802, some c813, some c159, some c809, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 57) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c475, c802, c813, c159, c809] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c159 := h 158 (by decide)
  have h4 : Entails.eval a c809 := derived809 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c807, some c802, some c798, some c393, some c387, some c645, some c475, some c814, some c111, some c502, some c277, some c353, some c56, some c78, some c363, some c812, some c201, some c3, some c267, some c270, some c208, some c323, some c317, some c290, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 57) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c807, c802, c798, c393, c387, c645, c475, c814, c111, c502, c277, c353, c56, c78, c363, c812, c201, c3, c267, c270, c208, c323, c317, c290] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c807 := derived807 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c798 := derived798 a h
  have h3 : Entails.eval a c393 := h 392 (by decide)
  have h4 : Entails.eval a c387 := h 386 (by decide)
  have h5 : Entails.eval a c645 := derived645 a h
  have h6 : Entails.eval a c475 := derived475 a h
  have h7 : Entails.eval a c814 := derived814 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c502 := derived502 a h
  have h10 : Entails.eval a c277 := h 276 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  have h14 : Entails.eval a c363 := h 362 (by decide)
  have h15 : Entails.eval a c812 := derived812 a h
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c3 := h 2 (by decide)
  have h18 : Entails.eval a c267 := h 266 (by decide)
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c208 := h 207 (by decide)
  have h21 : Entails.eval a c323 := h 322 (by decide)
  have h22 : Entails.eval a c317 := h 316 (by decide)
  have h23 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, false), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c387, some c56, some c342, some c218, some c107, some c359, some c262, some c225, some c31, some c257, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 57) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c393, c387, c56, c342, c218, c107, c359, c262, c225, c31, c257] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c342 := h 341 (by decide)
  have h4 : Entails.eval a c218 := h 217 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c225 := h 224 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c815, some c807, some c802, some c798, some c757, some c187, some c201, some c57, some c3, some c159, some c816, some c354, some c353, some c225, some c58, some c257, some c308, some c297, some c216, some c310, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 57) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c815, c807, c802, c798, c757, c187, c201, c57, c3, c159, c816, c354, c353, c225, c58, c257, c308, c297, c216, c310] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c815 := derived815 a h
  have h1 : Entails.eval a c807 := derived807 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c798 := derived798 a h
  have h4 : Entails.eval a c757 := derived757 a h
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c816 := derived816 a h
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c225 := h 224 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c297 := h 296 (by decide)
  have h18 : Entails.eval a c216 := h 215 (by decide)
  have h19 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c798, some c757, some c58, some c22, some c189, some c308, some c262, some c297, some c207, some c310, some c315, some c143, some c133, some c191, some c233, some c172, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 57) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c802, c798, c757, c58, c22, c189, c308, c262, c297, c207, c310, c315, c143, c133, c191, c233, c172] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c798 := derived798 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c308 := h 307 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c315 := h 314 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  have h14 : Entails.eval a c191 := h 190 (by decide)
  have h15 : Entails.eval a c233 := h 232 (by decide)
  have h16 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c819 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨35, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c812, some c56, some c363, some c78, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 57) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c353, c812, c56, c363, c78] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨10, by decide⟩, true), (⟨24, by decide⟩, true), (⟨48, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c387, some c393, some c819, some c57, some c251, some c56, some c342, some c78, some c107, some c67, some c12, some c362, some c191, some c225, some c23, some c135, some c282, some c41, some c290, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 57) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c2, c387, c393, c819, c57, c251, c56, c342, c78, c107, c67, c12, c362, c191, c225, c23, c135, c282, c41, c290] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c819 := derived819 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c362 := h 361 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c225 := h 224 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c135 := h 134 (by decide)
  have h17 : Entails.eval a c282 := h 281 (by decide)
  have h18 : Entails.eval a c41 := h 40 (by decide)
  have h19 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨25, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c107, some c132, some c67, some c12, some c155, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 57) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c78, c107, c132, c67, c12, c155] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨33, by decide⟩, false), (⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨48, by decide⟩, true), (⟨27, by decide⟩, false), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c290, some c132, some c320, some c282, some c152, some c133, some c225, some c3, some c233, some c153, some c172, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 57) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c273, c290, c132, c320, c282, c152, c133, c225, c3, c233, c153, c172] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c225 := h 224 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c233 := h 232 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c823 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨47, by decide⟩, true), (⟨43, by decide⟩, true), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c172, some c174, some c191, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 57) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c172, c174, c191] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c172 := h 171 (by decide)
  have h1 : Entails.eval a c174 := h 173 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c815, some c807, some c802, some c798, some c393, some c387, some c757, some c645, some c817, some c2, some c818, some c819, some c57, some c251, some c820, some c273, some c821, some c822, some c376, some c378, some c823, some c161, some c152, some c225, some c1, some c445, some c262, some c428, some c32, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 57) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c815, c807, c802, c798, c393, c387, c757, c645, c817, c2, c818, c819, c57, c251, c820, c273, c821, c822, c376, c378, c823, c161, c152, c225, c1, c445, c262, c428, c32] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c815 := derived815 a h
  have h1 : Entails.eval a c807 := derived807 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c798 := derived798 a h
  have h4 : Entails.eval a c393 := h 392 (by decide)
  have h5 : Entails.eval a c387 := h 386 (by decide)
  have h6 : Entails.eval a c757 := derived757 a h
  have h7 : Entails.eval a c645 := derived645 a h
  have h8 : Entails.eval a c817 := derived817 a h
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c818 := derived818 a h
  have h11 : Entails.eval a c819 := derived819 a h
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  have h14 : Entails.eval a c820 := derived820 a h
  have h15 : Entails.eval a c273 := h 272 (by decide)
  have h16 : Entails.eval a c821 := derived821 a h
  have h17 : Entails.eval a c822 := derived822 a h
  have h18 : Entails.eval a c376 := h 375 (by decide)
  have h19 : Entails.eval a c378 := h 377 (by decide)
  have h20 : Entails.eval a c823 := derived823 a h
  have h21 : Entails.eval a c161 := h 160 (by decide)
  have h22 : Entails.eval a c152 := h 151 (by decide)
  have h23 : Entails.eval a c225 := h 224 (by decide)
  have h24 : Entails.eval a c1 := h 0 (by decide)
  have h25 : Entails.eval a c445 := derived445 a h
  have h26 : Entails.eval a c262 := h 261 (by decide)
  have h27 : Entails.eval a c428 := derived428 a h
  have h28 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, true), (⟨43, by decide⟩, true), (⟨16, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c231, some c823, some c118, some c204, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 57) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c378, c231, c823, c118, c204] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c231 := h 230 (by decide)
  have h2 : Entails.eval a c823 := derived823 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨41, by decide⟩, true), (⟨48, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c320, some c290, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 57) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c315, c320, c290] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c798, some c393, some c387, some c757, some c645, some c807, some c815, some c824, some c111, some c105, some c84, some c48, some c56, some c92, some c29, some c825, some c363, some c826, some c779, some c172, some c823, some c191, some c90, some c7, some c445, some c257, some c266, some c657, some c241, some c23, some c215, some c50, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 57) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c802, c798, c393, c387, c757, c645, c807, c815, c824, c111, c105, c84, c48, c56, c92, c29, c825, c363, c826, c779, c172, c823, c191, c90, c7, c445, c257, c266, c657, c241, c23, c215, c50] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c798 := derived798 a h
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c757 := derived757 a h
  have h5 : Entails.eval a c645 := derived645 a h
  have h6 : Entails.eval a c807 := derived807 a h
  have h7 : Entails.eval a c815 := derived815 a h
  have h8 : Entails.eval a c824 := derived824 a h
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c29 := h 28 (by decide)
  have h16 : Entails.eval a c825 := derived825 a h
  have h17 : Entails.eval a c363 := h 362 (by decide)
  have h18 : Entails.eval a c826 := derived826 a h
  have h19 : Entails.eval a c779 := derived779 a h
  have h20 : Entails.eval a c172 := h 171 (by decide)
  have h21 : Entails.eval a c823 := derived823 a h
  have h22 : Entails.eval a c191 := h 190 (by decide)
  have h23 : Entails.eval a c90 := h 89 (by decide)
  have h24 : Entails.eval a c7 := h 6 (by decide)
  have h25 : Entails.eval a c445 := derived445 a h
  have h26 : Entails.eval a c257 := h 256 (by decide)
  have h27 : Entails.eval a c266 := h 265 (by decide)
  have h28 : Entails.eval a c657 := derived657 a h
  have h29 : Entails.eval a c241 := h 240 (by decide)
  have h30 : Entails.eval a c23 := h 22 (by decide)
  have h31 : Entails.eval a c215 := h 214 (by decide)
  have h32 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨11, by decide⟩, true), (⟨41, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c172, some c823, some c191, some c90, some c612, some c7, some c15, some c56, some c257, some c243, some c48, some c213, some c23, some c153, some c274, some c132, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 57) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c387, c172, c823, c191, c90, c612, c7, c15, c56, c257, c243, c48, c213, c23, c153, c274, c132] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c823 := derived823 a h
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c612 := derived612 a h
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c243 := h 242 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c153 := h 152 (by decide)
  have h15 : Entails.eval a c274 := h 273 (by decide)
  have h16 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨41, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c387, some c363, some c792, some c828, some c382, some c84, some c826, some c3, some c13, some c237, some c191, some c612, some c15, some c92, some c90, some c82, some c138, some c133, some c310, some c54, some c197, some c213, some c208, some c1, some c263, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 57) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c393, c387, c363, c792, c828, c382, c84, c826, c3, c13, c237, c191, c612, c15, c92, c90, c82, c138, c133, c310, c54, c197, c213, c208, c1, c263] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c363 := h 362 (by decide)
  have h3 : Entails.eval a c792 := derived792 a h
  have h4 : Entails.eval a c828 := derived828 a h
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c826 := derived826 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c237 := h 236 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c612 := derived612 a h
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c82 := h 81 (by decide)
  have h17 : Entails.eval a c138 := h 137 (by decide)
  have h18 : Entails.eval a c133 := h 132 (by decide)
  have h19 : Entails.eval a c310 := h 309 (by decide)
  have h20 : Entails.eval a c54 := h 53 (by decide)
  have h21 : Entails.eval a c197 := h 196 (by decide)
  have h22 : Entails.eval a c213 := h 212 (by decide)
  have h23 : Entails.eval a c208 := h 207 (by decide)
  have h24 : Entails.eval a c1 := h 0 (by decide)
  have h25 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c393, some c827, some c792, some c802, some c798, some c757, some c645, some c363, some c829, some c201, some c189, some c637, some c110, some c82, some c133, some c315, some c44, some c132, some c58, some c161, some c152, some c588, some c72, some c342, some c107, some c362, some c74, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 57) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c387, c393, c827, c792, c802, c798, c757, c645, c363, c829, c201, c189, c637, c110, c82, c133, c315, c44, c132, c58, c161, c152, c588, c72, c342, c107, c362, c74] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c827 := derived827 a h
  have h3 : Entails.eval a c792 := derived792 a h
  have h4 : Entails.eval a c802 := derived802 a h
  have h5 : Entails.eval a c798 := derived798 a h
  have h6 : Entails.eval a c757 := derived757 a h
  have h7 : Entails.eval a c645 := derived645 a h
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c829 := derived829 a h
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c637 := derived637 a h
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  have h17 : Entails.eval a c44 := h 43 (by decide)
  have h18 : Entails.eval a c132 := h 131 (by decide)
  have h19 : Entails.eval a c58 := h 57 (by decide)
  have h20 : Entails.eval a c161 := h 160 (by decide)
  have h21 : Entails.eval a c152 := h 151 (by decide)
  have h22 : Entails.eval a c588 := derived588 a h
  have h23 : Entails.eval a c72 := h 71 (by decide)
  have h24 : Entails.eval a c342 := h 341 (by decide)
  have h25 : Entails.eval a c107 := h 106 (by decide)
  have h26 : Entails.eval a c362 := h 361 (by decide)
  have h27 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c798, some c393, some c387, some c757, some c645, some c493, some c827, some c830, some c376, some c378, some c78, some c823, some c56, some c92, some c201, some c189, some c328, some c368, some c82, some c133, some c713, some c44, some c191, some c58, some c135, some c812, some c306, some c344, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 57) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c802, c798, c393, c387, c757, c645, c493, c827, c830, c376, c378, c78, c823, c56, c92, c201, c189, c328, c368, c82, c133, c713, c44, c191, c58, c135, c812, c306, c344] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c798 := derived798 a h
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c757 := derived757 a h
  have h5 : Entails.eval a c645 := derived645 a h
  have h6 : Entails.eval a c493 := derived493 a h
  have h7 : Entails.eval a c827 := derived827 a h
  have h8 : Entails.eval a c830 := derived830 a h
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c823 := derived823 a h
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c189 := h 188 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c368 := h 367 (by decide)
  have h19 : Entails.eval a c82 := h 81 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c713 := derived713 a h
  have h22 : Entails.eval a c44 := h 43 (by decide)
  have h23 : Entails.eval a c191 := h 190 (by decide)
  have h24 : Entails.eval a c58 := h 57 (by decide)
  have h25 : Entails.eval a c135 := h 134 (by decide)
  have h26 : Entails.eval a c812 := derived812 a h
  have h27 : Entails.eval a c306 := h 305 (by decide)
  have h28 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c387, some c376, some c378, some c328, some c823, some c56, some c201, some c204, some c11, some c792, some c75, some c16, some c713, some c191, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 57) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c393, c387, c376, c378, c328, c823, c56, c201, c204, c11, c792, c75, c16, c713, c191] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  have h5 : Entails.eval a c823 := derived823 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c792 := derived792 a h
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c713 := derived713 a h
  have h14 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c201, some c204, some c6, some c11, some c110, some c82, some c133, some c826, some c341, some c244, some c27, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 57) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c201, c204, c6, c11, c110, c82, c133, c826, c341, c244, c27] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c826 := derived826 a h
  have h8 : Entails.eval a c341 := h 340 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨2, by decide⟩, false), (⟨11, by decide⟩, true), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨27, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c393, some c792, some c363, some c44, some c826, some c13, some c382, some c191, some c823, some c15, some c88, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 57) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c387, c393, c792, c363, c44, c826, c13, c382, c191, c823, c15, c88] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c826 := derived826 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c823 := derived823 a h
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨45, by decide⟩, false), (⟨5, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c341, some c823, some c88, some c340, some c74, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 57) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c382, c341, c823, c88, c340, c74] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c382 := h 381 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c823 := derived823 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c340 := h 339 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true), (⟨45, by decide⟩, false), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c101, some c172, some c823, some c191, some c88, some c7, some c538, some c243, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 57) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c393, c101, c172, c823, c191, c88, c7, c538, c243] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c823 := derived823 a h
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c538 := derived538 a h
  have h8 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨4, by decide⟩, true), (⟨45, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c88, some c340, some c26, some c538, some c243, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 57) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c61, c88, c340, c26, c538, c243] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c538 := derived538 a h
  have h5 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c798, some c802, some c831, some c493, some c61, some c393, some c101, some c757, some c832, some c387, some c363, some c833, some c792, some c110, some c82, some c834, some c133, some c187, some c835, some c836, some c334, some c837, some c292, some c310, some c135, some c297, some c191, some c197, some c308, some c323, some c132, some c58, some c40, some c56, some c1, some c723, some c357, some c657, some c263, some c223, some c208, some c237, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 57) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c645, c798, c802, c831, c493, c61, c393, c101, c757, c832, c387, c363, c833, c792, c110, c82, c834, c133, c187, c835, c836, c334, c837, c292, c310, c135, c297, c191, c197, c308, c323, c132, c58, c40, c56, c1, c723, c357, c657, c263, c223, c208, c237] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c798 := derived798 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c831 := derived831 a h
  have h4 : Entails.eval a c493 := derived493 a h
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c393 := h 392 (by decide)
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c757 := derived757 a h
  have h9 : Entails.eval a c832 := derived832 a h
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c833 := derived833 a h
  have h13 : Entails.eval a c792 := derived792 a h
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c82 := h 81 (by decide)
  have h16 : Entails.eval a c834 := derived834 a h
  have h17 : Entails.eval a c133 := h 132 (by decide)
  have h18 : Entails.eval a c187 := h 186 (by decide)
  have h19 : Entails.eval a c835 := derived835 a h
  have h20 : Entails.eval a c836 := derived836 a h
  have h21 : Entails.eval a c334 := h 333 (by decide)
  have h22 : Entails.eval a c837 := derived837 a h
  have h23 : Entails.eval a c292 := h 291 (by decide)
  have h24 : Entails.eval a c310 := h 309 (by decide)
  have h25 : Entails.eval a c135 := h 134 (by decide)
  have h26 : Entails.eval a c297 := h 296 (by decide)
  have h27 : Entails.eval a c191 := h 190 (by decide)
  have h28 : Entails.eval a c197 := h 196 (by decide)
  have h29 : Entails.eval a c308 := h 307 (by decide)
  have h30 : Entails.eval a c323 := h 322 (by decide)
  have h31 : Entails.eval a c132 := h 131 (by decide)
  have h32 : Entails.eval a c58 := h 57 (by decide)
  have h33 : Entails.eval a c40 := h 39 (by decide)
  have h34 : Entails.eval a c56 := h 55 (by decide)
  have h35 : Entails.eval a c1 := h 0 (by decide)
  have h36 : Entails.eval a c723 := derived723 a h
  have h37 : Entails.eval a c357 := h 356 (by decide)
  have h38 : Entails.eval a c657 := derived657 a h
  have h39 : Entails.eval a c263 := h 262 (by decide)
  have h40 : Entails.eval a c223 := h 222 (by decide)
  have h41 : Entails.eval a c208 := h 207 (by decide)
  have h42 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨21, by decide⟩, true), (⟨42, by decide⟩, false), (⟨36, by decide⟩, false), (⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨38, by decide⟩, false), (⟨53, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c334, some c233, some c347, some c125, some c126, some c162, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 57) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c334, c233, c347, c125, c126, c162] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c334 := h 333 (by decide)
  have h1 : Entails.eval a c233 := h 232 (by decide)
  have h2 : Entails.eval a c347 := h 346 (by decide)
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c757, some c645, some c493, some c387, some c393, some c798, some c802, some c831, some c61, some c101, some c832, some c363, some c833, some c838, some c94, some c389, some c187, some c805, some c2, some c11, some c251, some c167, some c225, some c27, some c89, some c826, some c133, some c235, some c839, some c172, some c823, some c191, some c88, some c12, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 57) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c757, c645, c493, c387, c393, c798, c802, c831, c61, c101, c832, c363, c833, c838, c94, c389, c187, c805, c2, c11, c251, c167, c225, c27, c89, c826, c133, c235, c839, c172, c823, c191, c88, c12] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c757 := derived757 a h
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c393 := h 392 (by decide)
  have h5 : Entails.eval a c798 := derived798 a h
  have h6 : Entails.eval a c802 := derived802 a h
  have h7 : Entails.eval a c831 := derived831 a h
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c832 := derived832 a h
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c833 := derived833 a h
  have h13 : Entails.eval a c838 := derived838 a h
  have h14 : Entails.eval a c94 := h 93 (by decide)
  have h15 : Entails.eval a c389 := h 388 (by decide)
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c805 := derived805 a h
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c251 := h 250 (by decide)
  have h21 : Entails.eval a c167 := h 166 (by decide)
  have h22 : Entails.eval a c225 := h 224 (by decide)
  have h23 : Entails.eval a c27 := h 26 (by decide)
  have h24 : Entails.eval a c89 := h 88 (by decide)
  have h25 : Entails.eval a c826 := derived826 a h
  have h26 : Entails.eval a c133 := h 132 (by decide)
  have h27 : Entails.eval a c235 := h 234 (by decide)
  have h28 : Entails.eval a c839 := derived839 a h
  have h29 : Entails.eval a c172 := h 171 (by decide)
  have h30 : Entails.eval a c823 := derived823 a h
  have h31 : Entails.eval a c191 := h 190 (by decide)
  have h32 : Entails.eval a c88 := h 87 (by decide)
  have h33 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c840, some c99, some c61, some c757, some c645, some c94, some c389, some c391, some c367, some c101, some c334, some c112, some c347, some c346, some c362, some c359, some c67, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 57) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c493, c840, c99, c61, c757, c645, c94, c389, c391, c367, c101, c334, c112, c347, c346, c362, c359, c67] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c757 := derived757 a h
  have h5 : Entails.eval a c645 := derived645 a h
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c391 := h 390 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c334 := h 333 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c346 := h 345 (by decide)
  have h15 : Entails.eval a c362 := h 361 (by decide)
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c258, some c499, some c28, some c266, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 57) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c101, c258, c499, c28, c266] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c499 := derived499 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c362, some c64, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 57) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c356, c362, c64] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c362 := h 361 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c493, some c61, some c334, some c840, some c99, some c841, some c109, some c104, some c842, some c101, some c58, some c346, some c108, some c843, some c223, some c237, some c6, some c37, some c259, some c8, some c27, some c167, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 57) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c645, c493, c61, c334, c840, c99, c841, c109, c104, c842, c101, c58, c346, c108, c843, c223, c237, c6, c37, c259, c8, c27, c167] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c334 := h 333 (by decide)
  have h4 : Entails.eval a c840 := derived840 a h
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c842 := derived842 a h
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c346 := h 345 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c843 := derived843 a h
  have h15 : Entails.eval a c223 := h 222 (by decide)
  have h16 : Entails.eval a c237 := h 236 (by decide)
  have h17 : Entails.eval a c6 := h 5 (by decide)
  have h18 : Entails.eval a c37 := h 36 (by decide)
  have h19 : Entails.eval a c259 := h 258 (by decide)
  have h20 : Entails.eval a c8 := h 7 (by decide)
  have h21 : Entails.eval a c27 := h 26 (by decide)
  have h22 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨43, by decide⟩, false), (⟨6, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c844, some c645, some c493, some c61, some c334, some c382, some c840, some c99, some c841, some c109, some c104, some c842, some c223, some c237, some c255, some c6, some c227, some c167, some c587, some c169, some c200, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 57) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c844, c645, c493, c61, c334, c382, c840, c99, c841, c109, c104, c842, c223, c237, c255, c6, c227, c167, c587, c169, c200] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c334 := h 333 (by decide)
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c840 := derived840 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c842 := derived842 a h
  have h12 : Entails.eval a c223 := h 222 (by decide)
  have h13 : Entails.eval a c237 := h 236 (by decide)
  have h14 : Entails.eval a c255 := h 254 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c227 := h 226 (by decide)
  have h17 : Entails.eval a c167 := h 166 (by decide)
  have h18 : Entails.eval a c587 := derived587 a h
  have h19 : Entails.eval a c169 := h 168 (by decide)
  have h20 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨6, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c840, some c99, some c841, some c109, some c104, some c842, some c61, some c844, some c845, some c357, some c56, some c20, some c246, some c655, some c132, some c183, some c180, some c127, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 57) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c493, c840, c99, c841, c109, c104, c842, c61, c844, c845, c357, c56, c20, c246, c655, c132, c183, c180, c127] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c842 := derived842 a h
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c844 := derived844 a h
  have h9 : Entails.eval a c845 := derived845 a h
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c246 := h 245 (by decide)
  have h14 : Entails.eval a c655 := derived655 a h
  have h15 : Entails.eval a c132 := h 131 (by decide)
  have h16 : Entails.eval a c183 := h 182 (by decide)
  have h17 : Entails.eval a c180 := h 179 (by decide)
  have h18 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨38, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c340, some c56, some c20, some c655, some c132, some c183, some c180, some c174, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 57) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c357, c340, c56, c20, c655, c132, c183, c180, c174] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c340 := h 339 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c193, some c189, some c18, some c5, some c14, some c167, some c259, some c108, some c27, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 57) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c193, c189, c18, c5, c14, c167, c259, c108, c27] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c193 := h 192 (by decide)
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c259 := h 258 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c840, some c757, some c493, some c61, some c99, some c841, some c109, some c104, some c101, some c846, some c367, some c848, some c587, some c192, some c18, some c9, some c200, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 57) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c840, c757, c493, c61, c99, c841, c109, c104, c101, c846, c367, c848, c587, c192, c18, c9, c200] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c840 := derived840 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c846 := derived846 a h
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c848 := derived848 a h
  have h12 : Entails.eval a c587 := derived587 a h
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c109, some c9, some c132, some c1, some c192, some c655, some c792, some c672, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 57) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c104, c109, c9, c132, c1, c192, c655, c792, c672] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c655 := derived655 a h
  have h7 : Entails.eval a c792 := derived792 a h
  have h8 : Entails.eval a c672 := derived672 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨43, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c849, some c840, some c757, some c645, some c109, some c104, some c847, some c850, some c183, some c199, some c792, some c135, some c172, some c192, some c45, some c189, some c5, some c560, some c259, some c517, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 57) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c849, c840, c757, c645, c109, c104, c847, c850, c183, c199, c792, c135, c172, c192, c45, c189, c5, c560, c259, c517] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c849 := derived849 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c847 := derived847 a h
  have h7 : Entails.eval a c850 := derived850 a h
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c792 := derived792 a h
  have h11 : Entails.eval a c135 := h 134 (by decide)
  have h12 : Entails.eval a c172 := h 171 (by decide)
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c560 := derived560 a h
  have h18 : Entails.eval a c259 := h 258 (by decide)
  have h19 : Entails.eval a c517 := derived517 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c8, some c91, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 57) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c169, c8, c91] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, false), (⟨43, by decide⟩, true), (⟨6, by decide⟩, false), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c625, some c172, some c205, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 57) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c625, c172, c205] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c625 := derived625 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨39, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, false), (⟨43, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c849, some c757, some c645, some c853, some c189, some c169, some c91, some c341, some c10, some c74, some c107, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 57) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c849, c757, c645, c853, c189, c169, c91, c341, c10, c74, c107] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c849 := derived849 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c853 := derived853 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c757, some c645, some c172, some c189, some c176, some c17, some c91, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 57) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c757, c645, c172, c189, c176, c17, c91] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c757 := derived757 a h
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨39, by decide⟩, true), (⟨9, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c10, some c341, some c107, some c74, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 57) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c169, c10, c341, c107, c74] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c341 := h 340 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c341, some c27, some c255, some c242, some c126, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c341, c27, c255, c242, c126] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c341 := h 340 (by decide)
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c255 := h 254 (by decide)
  have h3 : Entails.eval a c242 := h 241 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨43, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c849, some c840, some c757, some c645, some c851, some c59, some c855, some c199, some c205, some c163, some c132, some c168, some c854, some c110, some c856, some c189, some c134, some c308, some c301, some c857, some c297, some c274, some c56, some c107, some c105, some c74, some c70, some c361, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c849, c840, c757, c645, c851, c59, c855, c199, c205, c163, c132, c168, c854, c110, c856, c189, c134, c308, c301, c857, c297, c274, c56, c107, c105, c74, c70, c361] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c849 := derived849 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c851 := derived851 a h
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c855 := derived855 a h
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c205 := h 204 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c132 := h 131 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c854 := derived854 a h
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c856 := derived856 a h
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c134 := h 133 (by decide)
  have h17 : Entails.eval a c308 := h 307 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c857 := derived857 a h
  have h20 : Entails.eval a c297 := h 296 (by decide)
  have h21 : Entails.eval a c274 := h 273 (by decide)
  have h22 : Entails.eval a c56 := h 55 (by decide)
  have h23 : Entails.eval a c107 := h 106 (by decide)
  have h24 : Entails.eval a c105 := h 104 (by decide)
  have h25 : Entails.eval a c74 := h 73 (by decide)
  have h26 : Entails.eval a c70 := h 69 (by decide)
  have h27 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, true), (⟨32, by decide⟩, true), (⟨16, by decide⟩, false), (⟨25, by decide⟩, false), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c757, some c645, some c857, some c297, some c318, some c299, some c90, some c340, some c26, some c74, some c241, some c243, some c167, some c130, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c189, c757, c645, c857, c297, c318, c299, c90, c340, c26, c74, c241, c243, c167, c130] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c857 := derived857 a h
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c340 := h 339 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c241 := h 240 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c167 := h 166 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨43, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c849, some c757, some c645, some c189, some c134, some c172, some c308, some c317, some c315, some c205, some c168, some c859, some c111, some c91, some c3, some c297, some c255, some c318, some c216, some c299, some c241, some c243, some c121, some c208, some c262, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c132, c849, c757, c645, c189, c134, c172, c308, c317, c315, c205, c168, c859, c111, c91, c3, c297, c255, c318, c216, c299, c241, c243, c121, c208, c262] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c308 := h 307 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c315 := h 314 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c859 := derived859 a h
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c297 := h 296 (by decide)
  have h17 : Entails.eval a c255 := h 254 (by decide)
  have h18 : Entails.eval a c318 := h 317 (by decide)
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c299 := h 298 (by decide)
  have h21 : Entails.eval a c241 := h 240 (by decide)
  have h22 : Entails.eval a c243 := h 242 (by decide)
  have h23 : Entails.eval a c121 := h 120 (by decide)
  have h24 : Entails.eval a c208 := h 207 (by decide)
  have h25 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨43, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c849, some c645, some c132, some c860, some c169, some c852, some c91, some c244, some c856, some c10, some c166, some c42, some c118, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c849, c645, c132, c860, c169, c852, c91, c244, c856, c10, c166, c42, c118] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c849 := derived849 a h
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c860 := derived860 a h
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c852 := derived852 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c244 := h 243 (by decide)
  have h8 : Entails.eval a c856 := derived856 a h
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c166 := h 165 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨43, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c849, some c757, some c645, some c858, some c861, some c200, some c199, some c135, some c172, some c189, some c196, some c176, some c2, some c91, some c8, some c244, some c269, some c236, some c128, some c133, some c263, some c316, some c321, some c206, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c849, c757, c645, c858, c861, c200, c199, c135, c172, c189, c196, c176, c2, c91, c8, c244, c269, c236, c128, c133, c263, c316, c321, c206] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c849 := derived849 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c858 := derived858 a h
  have h4 : Entails.eval a c861 := derived861 a h
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c176 := h 175 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c91 := h 90 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c244 := h 243 (by decide)
  have h16 : Entails.eval a c269 := h 268 (by decide)
  have h17 : Entails.eval a c236 := h 235 (by decide)
  have h18 : Entails.eval a c128 := h 127 (by decide)
  have h19 : Entails.eval a c133 := h 132 (by decide)
  have h20 : Entails.eval a c263 := h 262 (by decide)
  have h21 : Entails.eval a c316 := h 315 (by decide)
  have h22 : Entails.eval a c321 := h 320 (by decide)
  have h23 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c849, some c840, some c645, some c862, some c587, some c189, some c703, some c134, some c174, some c847, some c90, some c15, some c26, some c111, some c48, some c243, some c74, some c118, some c167, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c849, c840, c645, c862, c587, c189, c703, c134, c174, c847, c90, c15, c26, c111, c48, c243, c74, c118, c167] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c849 := derived849 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c862 := derived862 a h
  have h4 : Entails.eval a c587 := derived587 a h
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c703 := derived703 a h
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c174 := h 173 (by decide)
  have h9 : Entails.eval a c847 := derived847 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c48 := h 47 (by decide)
  have h15 : Entails.eval a c243 := h 242 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c118 := h 117 (by decide)
  have h18 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true), (⟨31, by decide⟩, false), (⟨1, by decide⟩, true), (⟨38, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c525, some c154, some c132, some c1, some c318, some c657, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c525, c154, c132, c1, c318, c657] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c525 := derived525 a h
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c657 := derived657 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c645, some c863, some c849, some c84, some c334, some c22, some c237, some c502, some c840, some c15, some c703, some c90, some c138, some c54, some c118, some c167, some c864, some c227, some c357, some c56, some c20, some c246, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c189, c645, c863, c849, c84, c334, c22, c237, c502, c840, c15, c703, c90, c138, c54, c118, c167, c864, c227, c357, c56, c20, c246] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c863 := derived863 a h
  have h3 : Entails.eval a c849 := derived849 a h
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c334 := h 333 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c237 := h 236 (by decide)
  have h8 : Entails.eval a c502 := derived502 a h
  have h9 : Entails.eval a c840 := derived840 a h
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c703 := derived703 a h
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c138 := h 137 (by decide)
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c167 := h 166 (by decide)
  have h17 : Entails.eval a c864 := derived864 a h
  have h18 : Entails.eval a c227 := h 226 (by decide)
  have h19 : Entails.eval a c357 := h 356 (by decide)
  have h20 : Entails.eval a c56 := h 55 (by decide)
  have h21 : Entails.eval a c20 := h 19 (by decide)
  have h22 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c166, some c200, some c167, some c70, some c227, some c132, some c107, some c525, some c1, some c265, some c658, some c225, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c166, c200, c167, c70, c227, c132, c107, c525, c1, c265, c658, c225] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c166 := h 165 (by decide)
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c227 := h 226 (by decide)
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c525 := derived525 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c658 := derived658 a h
  have h11 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨30, by decide⟩, false), (⟨24, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c288, some c27, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c55, c288, c27] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c288 := h 287 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨24, by decide⟩, true), (⟨48, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨6, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c867, some c290, some c42, some c275, some c20, some c655, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c867, c290, c42, c275, c20, c655] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c867 := derived867 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c655 := derived655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c863, some c849, some c84, some c334, some c22, some c237, some c382, some c502, some c868, some c118, some c865, some c866, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c645, c863, c849, c84, c334, c22, c237, c382, c502, c868, c118, c865, c866] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c849 := derived849 a h
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c334 := h 333 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c237 := h 236 (by decide)
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c502 := derived502 a h
  have h9 : Entails.eval a c868 := derived868 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c865 := derived865 a h
  have h12 : Entails.eval a c866 := derived866 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c849, some c645, some c863, some c382, some c84, some c334, some c22, some c502, some c237, some c868, some c118, some c869, some c587, some c169, some c200, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c849, c645, c863, c382, c84, c334, c22, c502, c237, c868, c118, c869, c587, c169, c200] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c849 := derived849 a h
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c863 := derived863 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c334 := h 333 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c502 := derived502 a h
  have h8 : Entails.eval a c237 := h 236 (by decide)
  have h9 : Entails.eval a c868 := derived868 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c869 := derived869 a h
  have h12 : Entails.eval a c587 := derived587 a h
  have h13 : Entails.eval a c169 := h 168 (by decide)
  have h14 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨48, by decide⟩, true), (⟨14, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c587, some c169, some c200, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c587, c169, c200] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c587 := derived587 a h
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨16, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c193, some c189, some c308, some c312, some c145, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c193, c189, c308, c312, c145] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c193 := h 192 (by decide)
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨48, by decide⟩, true), (⟨24, by decide⟩, true), (⟨53, by decide⟩, false), (⟨37, by decide⟩, true), (⟨38, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c299, some c216, some c243, some c258, some c226, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c299, c216, c243, c258, c226] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c299 := h 298 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c870, some c389, some c344, some c840, some c349, some c359, some c351, some c757, some c645, some c871, some c872, some c297, some c873, some c290, some c318, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c493, c870, c389, c344, c840, c349, c359, c351, c757, c645, c871, c872, c297, c873, c290, c318] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c870 := derived870 a h
  have h2 : Entails.eval a c389 := h 388 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c840 := derived840 a h
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c757 := derived757 a h
  have h9 : Entails.eval a c645 := derived645 a h
  have h10 : Entails.eval a c871 := derived871 a h
  have h11 : Entails.eval a c872 := derived872 a h
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c873 := derived873 a h
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨14, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c870, some c389, some c344, some c840, some c349, some c359, some c351, some c849, some c645, some c874, some c382, some c91, some c8, some c27, some c189, some c872, some c333, some c159, some c134, some c133, some c278, some c315, some c214, some c132, some c207, some c200, some c265, some c124, some c263, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c493, c870, c389, c344, c840, c349, c359, c351, c849, c645, c874, c382, c91, c8, c27, c189, c872, c333, c159, c134, c133, c278, c315, c214, c132, c207, c200, c265, c124, c263] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c870 := derived870 a h
  have h2 : Entails.eval a c389 := h 388 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c840 := derived840 a h
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c849 := derived849 a h
  have h9 : Entails.eval a c645 := derived645 a h
  have h10 : Entails.eval a c874 := derived874 a h
  have h11 : Entails.eval a c382 := h 381 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c27 := h 26 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c872 := derived872 a h
  have h17 : Entails.eval a c333 := h 332 (by decide)
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c278 := h 277 (by decide)
  have h22 : Entails.eval a c315 := h 314 (by decide)
  have h23 : Entails.eval a c214 := h 213 (by decide)
  have h24 : Entails.eval a c132 := h 131 (by decide)
  have h25 : Entails.eval a c207 := h 206 (by decide)
  have h26 : Entails.eval a c200 := h 199 (by decide)
  have h27 : Entails.eval a c265 := h 264 (by decide)
  have h28 : Entails.eval a c124 := h 123 (by decide)
  have h29 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c870, some c389, some c344, some c840, some c349, some c359, some c351, some c645, some c875, some c255, some c259, some c226, some c244, some c871, some c189, some c193, some c126, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c493, c870, c389, c344, c840, c349, c359, c351, c645, c875, c255, c259, c226, c244, c871, c189, c193, c126] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c870 := derived870 a h
  have h2 : Entails.eval a c389 := h 388 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c840 := derived840 a h
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c645 := derived645 a h
  have h9 : Entails.eval a c875 := derived875 a h
  have h10 : Entails.eval a c255 := h 254 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c226 := h 225 (by decide)
  have h13 : Entails.eval a c244 := h 243 (by decide)
  have h14 : Entails.eval a c871 := derived871 a h
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c193 := h 192 (by decide)
  have h17 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c876, some c493, some c870, some c389, some c344, some c840, some c349, some c359, some c351, some c757, some c645, some c189, some c193, some c872, some c290, some c297, some c318, some c402, some c873, some c270, some c259, some c126, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c876, c493, c870, c389, c344, c840, c349, c359, c351, c757, c645, c189, c193, c872, c290, c297, c318, c402, c873, c270, c259, c126] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c876 := derived876 a h
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c870 := derived870 a h
  have h3 : Entails.eval a c389 := h 388 (by decide)
  have h4 : Entails.eval a c344 := h 343 (by decide)
  have h5 : Entails.eval a c840 := derived840 a h
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c757 := derived757 a h
  have h10 : Entails.eval a c645 := derived645 a h
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c193 := h 192 (by decide)
  have h13 : Entails.eval a c872 := derived872 a h
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c297 := h 296 (by decide)
  have h16 : Entails.eval a c318 := h 317 (by decide)
  have h17 : Entails.eval a c402 := derived402 a h
  have h18 : Entails.eval a c873 := derived873 a h
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c259 := h 258 (by decide)
  have h21 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c757, some c877, some c587, some c169, some c176, some c199, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c757, c877, c587, c169, c176, c199] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c757 := derived757 a h
  have h1 : Entails.eval a c877 := derived877 a h
  have h2 : Entails.eval a c587 := derived587 a h
  have h3 : Entails.eval a c169 := h 168 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨48, by decide⟩, false), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c587, some c8, some c192, some c259, some c244, some c130, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c645, c587, c8, c192, c259, c244, c130] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c587 := derived587 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c244 := h 243 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c849, some c840, some c757, some c645, some c493, some c389, some c870, some c349, some c344, some c359, some c354, some c351, some c876, some c878, some c382, some c91, some c879, some c189, some c193, some c134, some c172, some c173, some c157, some c381, some c133, some c315, some c132, some c199, some c703, some c56, some c20, some c525, some c246, some c127, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c849, c840, c757, c645, c493, c389, c870, c349, c344, c359, c354, c351, c876, c878, c382, c91, c879, c189, c193, c134, c172, c173, c157, c381, c133, c315, c132, c199, c703, c56, c20, c525, c246, c127] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c849 := derived849 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c493 := derived493 a h
  have h5 : Entails.eval a c389 := h 388 (by decide)
  have h6 : Entails.eval a c870 := derived870 a h
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c351 := h 350 (by decide)
  have h12 : Entails.eval a c876 := derived876 a h
  have h13 : Entails.eval a c878 := derived878 a h
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  have h16 : Entails.eval a c879 := derived879 a h
  have h17 : Entails.eval a c189 := h 188 (by decide)
  have h18 : Entails.eval a c193 := h 192 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c172 := h 171 (by decide)
  have h21 : Entails.eval a c173 := h 172 (by decide)
  have h22 : Entails.eval a c157 := h 156 (by decide)
  have h23 : Entails.eval a c381 := h 380 (by decide)
  have h24 : Entails.eval a c133 := h 132 (by decide)
  have h25 : Entails.eval a c315 := h 314 (by decide)
  have h26 : Entails.eval a c132 := h 131 (by decide)
  have h27 : Entails.eval a c199 := h 198 (by decide)
  have h28 : Entails.eval a c703 := derived703 a h
  have h29 : Entails.eval a c56 := h 55 (by decide)
  have h30 : Entails.eval a c20 := h 19 (by decide)
  have h31 : Entails.eval a c525 := derived525 a h
  have h32 : Entails.eval a c246 := h 245 (by decide)
  have h33 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨1, by decide⟩, true), (⟨15, by decide⟩, true), (⟨36, by decide⟩, false), (⟨4, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c359, some c525, some c64, some c7, some c112, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c354, c359, c525, c64, c7, c112] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c525 := derived525 a h
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨36, by decide⟩, false), (⟨38, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c391, some c351, some c97, some c362, some c109, some c112, some c67, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c344, c391, c351, c97, c362, c109, c112, c67] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c362 := h 361 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c525, some c65, some c64, some c110, some c112, some c31, some c34, some c262, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c20, c525, c65, c64, c110, c112, c31, c34, c262] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c525 := derived525 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c31, some c267, some c262, some c218, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c34, c31, c267, c262, c218] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c840, some c757, some c645, some c493, some c849, some c880, some c367, some c84, some c58, some c96, some c334, some c349, some c882, some c354, some c358, some c359, some c351, some c883, some c107, some c104, some c884, some c258, some c226, some c217, some c266, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c840, c757, c645, c493, c849, c880, c367, c84, c58, c96, c334, c349, c882, c354, c358, c359, c351, c883, c107, c104, c884, c258, c226, c217, c266] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c840 := derived840 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c493 := derived493 a h
  have h4 : Entails.eval a c849 := derived849 a h
  have h5 : Entails.eval a c880 := derived880 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c334 := h 333 (by decide)
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c882 := derived882 a h
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c351 := h 350 (by decide)
  have h17 : Entails.eval a c883 := derived883 a h
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c104 := h 103 (by decide)
  have h20 : Entails.eval a c884 := derived884 a h
  have h21 : Entails.eval a c258 := h 257 (by decide)
  have h22 : Entails.eval a c226 := h 225 (by decide)
  have h23 : Entails.eval a c217 := h 216 (by decide)
  have h24 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨19, by decide⟩, true), (⟨22, by decide⟩, true), (⟨34, by decide⟩, false), (⟨36, by decide⟩, false), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c359, some c64, some c525, some c20, some c56, some c881, some c109, some c112, some c183, some c31, some c26, some c34, some c263, some c163, some c111, some c128, some c172, some c10, some c204, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c354, c359, c64, c525, c20, c56, c881, c109, c112, c183, c31, c26, c34, c263, c163, c111, c128, c172, c10, c204] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c525 := derived525 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c881 := derived881 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c111 := h 110 (by decide)
  have h16 : Entails.eval a c128 := h 127 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c10 := h 9 (by decide)
  have h19 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c757, some c840, some c645, some c885, some c376, some c367, some c378, some c587, some c174, some c189, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c757, c840, c645, c885, c376, c367, c378, c587, c174, c189] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c757 := derived757 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c885 := derived885 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c587 := derived587 a h
  have h8 : Entails.eval a c174 := h 173 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨17, by decide⟩, false), (⟨39, by decide⟩, true), (⟨11, by decide⟩, true), (⟨36, by decide⟩, false), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c56, some c525, some c246, some c223, some c3, some c358, some c111, some c65, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c354, c56, c525, c246, c223, c3, c358, c111, c65] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c525 := derived525 a h
  have h3 : Entails.eval a c246 := h 245 (by decide)
  have h4 : Entails.eval a c223 := h 222 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨36, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c376, some c172, some c199, some c163, some c853, some c1, some c888, some c344, some c57, some c328, some c110, some c56, some c525, some c65, some c246, some c223, some c361, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c78, c376, c172, c199, c163, c853, c1, c888, c344, c57, c328, c110, c56, c525, c65, c246, c223, c361] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c163 := h 162 (by decide)
  have h5 : Entails.eval a c853 := derived853 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c888 := derived888 a h
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c525 := derived525 a h
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c246 := h 245 (by decide)
  have h16 : Entails.eval a c223 := h 222 (by decide)
  have h17 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨16, by decide⟩, true), (⟨36, by decide⟩, false), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨15, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c205, some c199, some c9, some c1, some c10, some c91, some c110, some c139, some c57, some c53, some c354, some c140, some c655, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c205, c199, c9, c1, c10, c91, c110, c139, c57, c53, c354, c140, c655] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c205 := h 204 (by decide)
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c655 := derived655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c885, some c78, some c887, some c757, some c840, some c376, some c367, some c389, some c493, some c889, some c189, some c890, some c855, some c176, some c91, some c8, some c10, some c255, some c244, some c180, some c886, some c56, some c344, some c328, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c645, c885, c78, c887, c757, c840, c376, c367, c389, c493, c889, c189, c890, c855, c176, c91, c8, c10, c255, c244, c180, c886, c56, c344, c328] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c885 := derived885 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c887 := derived887 a h
  have h4 : Entails.eval a c757 := derived757 a h
  have h5 : Entails.eval a c840 := derived840 a h
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c493 := derived493 a h
  have h10 : Entails.eval a c889 := derived889 a h
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c890 := derived890 a h
  have h13 : Entails.eval a c855 := derived855 a h
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  have h16 : Entails.eval a c8 := h 7 (by decide)
  have h17 : Entails.eval a c10 := h 9 (by decide)
  have h18 : Entails.eval a c255 := h 254 (by decide)
  have h19 : Entails.eval a c244 := h 243 (by decide)
  have h20 : Entails.eval a c180 := h 179 (by decide)
  have h21 : Entails.eval a c886 := derived886 a h
  have h22 : Entails.eval a c56 := h 55 (by decide)
  have h23 : Entails.eval a c344 := h 343 (by decide)
  have h24 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c757, some c840, some c645, some c885, some c376, some c367, some c78, some c493, some c891, some c349, some c328, some c20, some c56, some c246, some c887, some c183, some c655, some c525, some c59, some c378, some c141, some c10, some c308, some c111, some c295, some c293, some c34, some c51, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c757, c840, c645, c885, c376, c367, c78, c493, c891, c349, c328, c20, c56, c246, c887, c183, c655, c525, c59, c378, c141, c10, c308, c111, c295, c293, c34, c51] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c757 := derived757 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c645 := derived645 a h
  have h3 : Entails.eval a c885 := derived885 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c493 := derived493 a h
  have h8 : Entails.eval a c891 := derived891 a h
  have h9 : Entails.eval a c349 := h 348 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c246 := h 245 (by decide)
  have h14 : Entails.eval a c887 := derived887 a h
  have h15 : Entails.eval a c183 := h 182 (by decide)
  have h16 : Entails.eval a c655 := derived655 a h
  have h17 : Entails.eval a c525 := derived525 a h
  have h18 : Entails.eval a c59 := h 58 (by decide)
  have h19 : Entails.eval a c378 := h 377 (by decide)
  have h20 : Entails.eval a c141 := h 140 (by decide)
  have h21 : Entails.eval a c10 := h 9 (by decide)
  have h22 : Entails.eval a c308 := h 307 (by decide)
  have h23 : Entails.eval a c111 := h 110 (by decide)
  have h24 : Entails.eval a c295 := h 294 (by decide)
  have h25 : Entails.eval a c293 := h 292 (by decide)
  have h26 : Entails.eval a c34 := h 33 (by decide)
  have h27 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c887, some c757, some c840, some c645, some c885, some c376, some c367, some c493, some c78, some c891, some c349, some c59, some c328, some c56, some c20, some c525, some c183, some c246, some c892, some c189, some c172, some c853, some c3, some c205, some c109, some c112, some c111, some c126, some c31, some c38, some c269, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c887, c757, c840, c645, c885, c376, c367, c493, c78, c891, c349, c59, c328, c56, c20, c525, c183, c246, c892, c189, c172, c853, c3, c205, c109, c112, c111, c126, c31, c38, c269] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c887 := derived887 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c840 := derived840 a h
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c885 := derived885 a h
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c493 := derived493 a h
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c891 := derived891 a h
  have h10 : Entails.eval a c349 := h 348 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c525 := derived525 a h
  have h16 : Entails.eval a c183 := h 182 (by decide)
  have h17 : Entails.eval a c246 := h 245 (by decide)
  have h18 : Entails.eval a c892 := derived892 a h
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c172 := h 171 (by decide)
  have h21 : Entails.eval a c853 := derived853 a h
  have h22 : Entails.eval a c3 := h 2 (by decide)
  have h23 : Entails.eval a c205 := h 204 (by decide)
  have h24 : Entails.eval a c109 := h 108 (by decide)
  have h25 : Entails.eval a c112 := h 111 (by decide)
  have h26 : Entails.eval a c111 := h 110 (by decide)
  have h27 : Entails.eval a c126 := h 125 (by decide)
  have h28 : Entails.eval a c31 := h 30 (by decide)
  have h29 : Entails.eval a c38 := h 37 (by decide)
  have h30 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived893

end CochromaticTwenty.Certificates.B16_0_0
