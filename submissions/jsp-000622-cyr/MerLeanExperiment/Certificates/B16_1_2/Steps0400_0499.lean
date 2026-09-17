import MerLeanExperiment.Certificates.B16_1_2.Steps0300_0399

/-! Generated from the actual pinned b16_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c794 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c91, some c61, some c291, some c321, some c85, some c37, some c227, some c253, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 57) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c57, c91, c61, c291, c321, c85, c37, c227, c253] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c129, some c11, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 57) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c257, c129, c11] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c129 := h 128 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c793, some c751, some c655, some c122, some c2, some c30, some c57, some c260, some c216, some c349, some c83, some c794, some c84, some c281, some c321, some c227, some c60, some c124, some c795, some c46, some c253, some c269, some c9, some c240, some c497, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 57) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c793, c751, c655, c122, c2, c30, c57, c260, c216, c349, c83, c794, c84, c281, c321, c227, c60, c124, c795, c46, c253, c269, c9, c240, c497] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c793 := derived793 a h
  have h1 : Entails.eval a c751 := derived751 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c349 := h 348 (by decide)
  have h10 : Entails.eval a c83 := h 82 (by decide)
  have h11 : Entails.eval a c794 := derived794 a h
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c321 := h 320 (by decide)
  have h15 : Entails.eval a c227 := h 226 (by decide)
  have h16 : Entails.eval a c60 := h 59 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c795 := derived795 a h
  have h19 : Entails.eval a c46 := h 45 (by decide)
  have h20 : Entails.eval a c253 := h 252 (by decide)
  have h21 : Entails.eval a c269 := h 268 (by decide)
  have h22 : Entails.eval a c9 := h 8 (by decide)
  have h23 : Entails.eval a c240 := h 239 (by decide)
  have h24 : Entails.eval a c497 := derived497 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c256, some c128, some c9, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 57) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c256, c128, c9] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c793, some c391, some c655, some c796, some c36, some c8, some c260, some c762, some c30, some c210, some c121, some c75, some c733, some c797, some c217, some c711, some c377, some c291, some c221, some c140, some c200, some c153, some c533, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 57) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c793, c391, c655, c796, c36, c8, c260, c762, c30, c210, c121, c75, c733, c797, c217, c711, c377, c291, c221, c140, c200, c153, c533] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c793 := derived793 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c796 := derived796 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c762 := derived762 a h
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c210 := h 209 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c733 := derived733 a h
  have h13 : Entails.eval a c797 := derived797 a h
  have h14 : Entails.eval a c217 := h 216 (by decide)
  have h15 : Entails.eval a c711 := derived711 a h
  have h16 : Entails.eval a c377 := h 376 (by decide)
  have h17 : Entails.eval a c291 := h 290 (by decide)
  have h18 : Entails.eval a c221 := h 220 (by decide)
  have h19 : Entails.eval a c140 := h 139 (by decide)
  have h20 : Entails.eval a c200 := h 199 (by decide)
  have h21 : Entails.eval a c153 := h 152 (by decide)
  have h22 : Entails.eval a c533 := derived533 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c221, some c321, some c220, some c436, some c112, some c52, some c264, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c221, c321, c220, c436, c112, c52, c264] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c221 := h 220 (by decide)
  have h1 : Entails.eval a c321 := h 320 (by decide)
  have h2 : Entails.eval a c220 := h 219 (by decide)
  have h3 : Entails.eval a c436 := derived436 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c727, some c8, some c36, some c799, some c140, some c200, some c15, some c533, some c436, some c153, some c321, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c727, c8, c36, c799, c140, c200, c15, c533, c436, c153, c321] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c727 := derived727 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c799 := derived799 a h
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c533 := derived533 a h
  have h8 : Entails.eval a c436 := derived436 a h
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c793, some c751, some c391, some c655, some c798, some c727, some c36, some c8, some c260, some c30, some c210, some c121, some c349, some c65, some c800, some c217, some c270, some c271, some c128, some c509, some c141, some c71, some c358, some c112, some c287, some c316, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c793, c751, c391, c655, c798, c727, c36, c8, c260, c30, c210, c121, c349, c65, c800, c217, c270, c271, c128, c509, c141, c71, c358, c112, c287, c316] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c793 := derived793 a h
  have h1 : Entails.eval a c751 := derived751 a h
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c798 := derived798 a h
  have h5 : Entails.eval a c727 := derived727 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c800 := derived800 a h
  have h15 : Entails.eval a c217 := h 216 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c271 := h 270 (by decide)
  have h18 : Entails.eval a c128 := h 127 (by decide)
  have h19 : Entails.eval a c509 := derived509 a h
  have h20 : Entails.eval a c141 := h 140 (by decide)
  have h21 : Entails.eval a c71 := h 70 (by decide)
  have h22 : Entails.eval a c358 := h 357 (by decide)
  have h23 : Entails.eval a c112 := h 111 (by decide)
  have h24 : Entails.eval a c287 := h 286 (by decide)
  have h25 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨39, by decide⟩, false), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨38, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c358, some c112, some c52, some c238, some c264, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c71, c358, c112, c52, c238, c264] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c238 := h 237 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c655, some c15, some c91, some c112, some c175, some c389, some c367, some c662, some c194, some c183, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c391, c655, c15, c91, c112, c175, c389, c367, c662, c194, c183] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c662 := derived662 a h
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c793, some c260, some c30, some c210, some c75, some c349, some c121, some c655, some c391, some c727, some c801, some c751, some c256, some c270, some c271, some c509, some c214, some c322, some c802, some c141, some c128, some c25, some c803, some c117, some c629, some c27, some c207, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c793, c260, c30, c210, c75, c349, c121, c655, c391, c727, c801, c751, c256, c270, c271, c509, c214, c322, c802, c141, c128, c25, c803, c117, c629, c27, c207] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c793 := derived793 a h
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c655 := derived655 a h
  have h8 : Entails.eval a c391 := h 390 (by decide)
  have h9 : Entails.eval a c727 := derived727 a h
  have h10 : Entails.eval a c801 := derived801 a h
  have h11 : Entails.eval a c751 := derived751 a h
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c509 := derived509 a h
  have h16 : Entails.eval a c214 := h 213 (by decide)
  have h17 : Entails.eval a c322 := h 321 (by decide)
  have h18 : Entails.eval a c802 := derived802 a h
  have h19 : Entails.eval a c141 := h 140 (by decide)
  have h20 : Entails.eval a c128 := h 127 (by decide)
  have h21 : Entails.eval a c25 := h 24 (by decide)
  have h22 : Entails.eval a c803 := derived803 a h
  have h23 : Entails.eval a c117 := h 116 (by decide)
  have h24 : Entails.eval a c629 := derived629 a h
  have h25 : Entails.eval a c27 := h 26 (by decide)
  have h26 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨39, by decide⟩, false), (⟨16, by decide⟩, true), (⟨40, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c629, some c27, some c207, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c117, c629, c27, c207] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c727, some c801, some c793, some c260, some c30, some c210, some c121, some c349, some c75, some c804, some c217, some c308, some c323, some c322, some c733, some c214, some c146, some c288, some c25, some c137, some c40, some c185, some c377, some c805, some c112, some c662, some c347, some c331, some c231, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c655, c391, c727, c801, c793, c260, c30, c210, c121, c349, c75, c804, c217, c308, c323, c322, c733, c214, c146, c288, c25, c137, c40, c185, c377, c805, c112, c662, c347, c331, c231] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c727 := derived727 a h
  have h3 : Entails.eval a c801 := derived801 a h
  have h4 : Entails.eval a c793 := derived793 a h
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c349 := h 348 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c804 := derived804 a h
  have h12 : Entails.eval a c217 := h 216 (by decide)
  have h13 : Entails.eval a c308 := h 307 (by decide)
  have h14 : Entails.eval a c323 := h 322 (by decide)
  have h15 : Entails.eval a c322 := h 321 (by decide)
  have h16 : Entails.eval a c733 := derived733 a h
  have h17 : Entails.eval a c214 := h 213 (by decide)
  have h18 : Entails.eval a c146 := h 145 (by decide)
  have h19 : Entails.eval a c288 := h 287 (by decide)
  have h20 : Entails.eval a c25 := h 24 (by decide)
  have h21 : Entails.eval a c137 := h 136 (by decide)
  have h22 : Entails.eval a c40 := h 39 (by decide)
  have h23 : Entails.eval a c185 := h 184 (by decide)
  have h24 : Entails.eval a c377 := h 376 (by decide)
  have h25 : Entails.eval a c805 := derived805 a h
  have h26 : Entails.eval a c112 := h 111 (by decide)
  have h27 : Entails.eval a c662 := derived662 a h
  have h28 : Entails.eval a c347 := h 346 (by decide)
  have h29 : Entails.eval a c331 := h 330 (by decide)
  have h30 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, true), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨26, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c91, some c112, some c304, some c258, some c264, some c64, some c220, some c316, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c91, c112, c304, c258, c264, c64, c220, c316] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c220 := h 219 (by decide)
  have h7 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c30, some c210, some c73, some c349, some c235, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c30, c210, c73, c349, c235] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c210 := h 209 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  have h4 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c727, some c806, some c44, some c801, some c793, some c751, some c53, some c807, some c117, some c55, some c264, some c275, some c12, some c51, some c136, some c808, some c130, some c20, some c142, some c73, some c349, some c235, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c655, c391, c727, c806, c44, c801, c793, c751, c53, c807, c117, c55, c264, c275, c12, c51, c136, c808, c130, c20, c142, c73, c349, c235] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c727 := derived727 a h
  have h3 : Entails.eval a c806 := derived806 a h
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c801 := derived801 a h
  have h6 : Entails.eval a c793 := derived793 a h
  have h7 : Entails.eval a c751 := derived751 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c807 := derived807 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c275 := h 274 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c808 := derived808 a h
  have h18 : Entails.eval a c130 := h 129 (by decide)
  have h19 : Entails.eval a c20 := h 19 (by decide)
  have h20 : Entails.eval a c142 := h 141 (by decide)
  have h21 : Entails.eval a c73 := h 72 (by decide)
  have h22 : Entails.eval a c349 := h 348 (by decide)
  have h23 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨48, by decide⟩, false), (⟨24, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c123, some c196, some c235, some c77, some c169, some c144, some c180, some c188, some c96, some c373, some c300, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c123, c196, c235, c77, c169, c144, c180, c188, c96, c373, c300] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c123 := h 122 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c235 := h 234 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c373 := h 372 (by decide)
  have h10 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨26, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c322, some c303, some c277, some c377, some c360, some c304, some c281, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c322, c303, c277, c377, c360, c304, c281] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c793, some c809, some c121, some c30, some c2, some c655, some c391, some c727, some c806, some c44, some c801, some c258, some c272, some c273, some c130, some c51, some c123, some c60, some c810, some c349, some c811, some c214, some c222, some c81, some c327, some c144, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c793, c809, c121, c30, c2, c655, c391, c727, c806, c44, c801, c258, c272, c273, c130, c51, c123, c60, c810, c349, c811, c214, c222, c81, c327, c144] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c793 := derived793 a h
  have h1 : Entails.eval a c809 := derived809 a h
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c655 := derived655 a h
  have h6 : Entails.eval a c391 := h 390 (by decide)
  have h7 : Entails.eval a c727 := derived727 a h
  have h8 : Entails.eval a c806 := derived806 a h
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c801 := derived801 a h
  have h11 : Entails.eval a c258 := h 257 (by decide)
  have h12 : Entails.eval a c272 := h 271 (by decide)
  have h13 : Entails.eval a c273 := h 272 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c123 := h 122 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c810 := derived810 a h
  have h19 : Entails.eval a c349 := h 348 (by decide)
  have h20 : Entails.eval a c811 := derived811 a h
  have h21 : Entails.eval a c214 := h 213 (by decide)
  have h22 : Entails.eval a c222 := h 221 (by decide)
  have h23 : Entails.eval a c81 := h 80 (by decide)
  have h24 : Entails.eval a c327 := h 326 (by decide)
  have h25 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c222, some c81, some c327, some c144, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c214, c222, c81, c327, c144] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c222 := h 221 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c813, some c131, some c146, some c70, some c81, some c163, some c203, some c201, some c27, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 57) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c196, c813, c131, c146, c70, c81, c163, c203, c201, c27] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c163 := h 162 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, true), (⟨10, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c205, some c204, some c194, some c154, some c314, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 57) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c205, c204, c194, c154, c314] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c205 := h 204 (by decide)
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c814, some c131, some c316, some c146, some c212, some c81, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 57) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c813, c814, c131, c316, c146, c212, c81] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c814 := derived814 a h
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨34, by decide⟩, true), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨1, by decide⟩, false), (⟨26, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c30, some c2, some c727, some c55, some c60, some c815, some c816, some c257, some c129, some c276, some c194, some c131, some c214, some c228, some c70, some c321, some c277, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 57) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c121, c30, c2, c727, c55, c60, c815, c816, c257, c129, c276, c194, c131, c214, c228, c70, c321, c277] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c727 := derived727 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c815 := derived815 a h
  have h7 : Entails.eval a c816 := derived816 a h
  have h8 : Entails.eval a c257 := h 256 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  have h11 : Entails.eval a c194 := h 193 (by decide)
  have h12 : Entails.eval a c131 := h 130 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c321 := h 320 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c795, some c51, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 57) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c795, c51] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c795 := derived795 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c819 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c809, some c655, some c391, some c727, some c806, some c793, some c121, some c2, some c30, some c818, some c123, some c812, some c44, some c801, some c751, some c349, some c811, some c817, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 57) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c809, c655, c391, c727, c806, c793, c121, c2, c30, c818, c123, c812, c44, c801, c751, c349, c811, c817] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c809 := derived809 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c727 := derived727 a h
  have h4 : Entails.eval a c806 := derived806 a h
  have h5 : Entails.eval a c793 := derived793 a h
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c818 := derived818 a h
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c812 := derived812 a h
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c801 := derived801 a h
  have h14 : Entails.eval a c751 := derived751 a h
  have h15 : Entails.eval a c349 := h 348 (by decide)
  have h16 : Entails.eval a c811 := derived811 a h
  have h17 : Entails.eval a c817 := derived817 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c793, some c391, some c655, some c727, some c806, some c809, some c121, some c2, some c30, some c812, some c818, some c819, some c237, some c77, some c235, some c257, some c129, some c194, some c167, some c206, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 57) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c793, c391, c655, c727, c806, c809, c121, c2, c30, c812, c818, c819, c237, c77, c235, c257, c129, c194, c167, c206] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c793 := derived793 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c727 := derived727 a h
  have h4 : Entails.eval a c806 := derived806 a h
  have h5 : Entails.eval a c809 := derived809 a h
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c812 := derived812 a h
  have h10 : Entails.eval a c818 := derived818 a h
  have h11 : Entails.eval a c819 := derived819 a h
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c77 := h 76 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c129 := h 128 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c167 := h 166 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨30, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c146, some c131, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 57) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c214, c146, c131] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨9, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c237, some c258, some c130, some c196, some c169, some c203, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 57) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c237, c258, c130, c196, c169, c203] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c237 := h 236 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c823 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c820, some c801, some c793, some c655, some c121, some c2, some c30, some c57, some c260, some c308, some c322, some c9, some c85, some c292, some c44, some c821, some c81, some c822, some c83, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 57) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c820, c801, c793, c655, c121, c2, c30, c57, c260, c308, c322, c9, c85, c292, c44, c821, c81, c822, c83] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c820 := derived820 a h
  have h1 : Entails.eval a c801 := derived801 a h
  have h2 : Entails.eval a c793 := derived793 a h
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c322 := h 321 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c821 := derived821 a h
  have h16 : Entails.eval a c81 := h 80 (by decide)
  have h17 : Entails.eval a c822 := derived822 a h
  have h18 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c823, some c820, some c801, some c793, some c751, some c30, some c57, some c308, some c323, some c107, some c61, some c389, some c258, some c106, some c32, some c124, some c316, some c60, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 57) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c823, c820, c801, c793, c751, c30, c57, c308, c323, c107, c61, c389, c258, c106, c32, c124, c316, c60] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c823 := derived823 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c801 := derived801 a h
  have h3 : Entails.eval a c793 := derived793 a h
  have h4 : Entails.eval a c751 := derived751 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c308 := h 307 (by decide)
  have h8 : Entails.eval a c323 := h 322 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c389 := h 388 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c316 := h 315 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c824, some c122, some c823, some c820, some c801, some c793, some c751, some c655, some c260, some c44, some c53, some c807, some c258, some c272, some c107, some c51, some c308, some c124, some c29, some c55, some c253, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 57) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c824, c122, c823, c820, c801, c793, c751, c655, c260, c44, c53, c807, c258, c272, c107, c51, c308, c124, c29, c55, c253] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c824 := derived824 a h
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c823 := derived823 a h
  have h3 : Entails.eval a c820 := derived820 a h
  have h4 : Entails.eval a c801 := derived801 a h
  have h5 : Entails.eval a c793 := derived793 a h
  have h6 : Entails.eval a c751 := derived751 a h
  have h7 : Entails.eval a c655 := derived655 a h
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c807 := derived807 a h
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c29 := h 28 (by decide)
  have h19 : Entails.eval a c55 := h 54 (by decide)
  have h20 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c825, some c824, some c122, some c823, some c820, some c801, some c793, some c751, some c655, some c308, some c217, some c59, some c256, some c253, some c44, some c53, some c55, some c220, some c807, some c124, some c327, some c58, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 57) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c825, c824, c122, c823, c820, c801, c793, c751, c655, c308, c217, c59, c256, c253, c44, c53, c55, c220, c807, c124, c327, c58] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c825 := derived825 a h
  have h1 : Entails.eval a c824 := derived824 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c823 := derived823 a h
  have h4 : Entails.eval a c820 := derived820 a h
  have h5 : Entails.eval a c801 := derived801 a h
  have h6 : Entails.eval a c793 := derived793 a h
  have h7 : Entails.eval a c751 := derived751 a h
  have h8 : Entails.eval a c655 := derived655 a h
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c217 := h 216 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c253 := h 252 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c53 := h 52 (by decide)
  have h16 : Entails.eval a c55 := h 54 (by decide)
  have h17 : Entails.eval a c220 := h 219 (by decide)
  have h18 : Entails.eval a c807 := derived807 a h
  have h19 : Entails.eval a c124 := h 123 (by decide)
  have h20 : Entails.eval a c327 := h 326 (by decide)
  have h21 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c655, some c793, some c820, some c823, some c824, some c122, some c825, some c210, some c75, some c826, some c9, some c85, some c107, some c803, some c389, some c106, some c124, some c758, some c377, some c379, some c698, some c174, some c44, some c245, some c146, some c271, some c711, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 57) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c391, c655, c793, c820, c823, c824, c122, c825, c210, c75, c826, c9, c85, c107, c803, c389, c106, c124, c758, c377, c379, c698, c174, c44, c245, c146, c271, c711] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c793 := derived793 a h
  have h3 : Entails.eval a c820 := derived820 a h
  have h4 : Entails.eval a c823 := derived823 a h
  have h5 : Entails.eval a c824 := derived824 a h
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c825 := derived825 a h
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c826 := derived826 a h
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c803 := derived803 a h
  have h15 : Entails.eval a c389 := h 388 (by decide)
  have h16 : Entails.eval a c106 := h 105 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c758 := derived758 a h
  have h19 : Entails.eval a c377 := h 376 (by decide)
  have h20 : Entails.eval a c379 := h 378 (by decide)
  have h21 : Entails.eval a c698 := derived698 a h
  have h22 : Entails.eval a c174 := h 173 (by decide)
  have h23 : Entails.eval a c44 := h 43 (by decide)
  have h24 : Entails.eval a c245 := h 244 (by decide)
  have h25 : Entails.eval a c146 := h 145 (by decide)
  have h26 : Entails.eval a c271 := h 270 (by decide)
  have h27 : Entails.eval a c711 := derived711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c85, some c174, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 57) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c9, c85, c174] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨4, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c349, some c391, some c827, some c90, some c14, some c655, some c116, some c751, some c828, some c707, some c34, some c711, some c256, some c253, some c216, some c220, some c54, some c308, some c124, some c59, some c58, some c327, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 57) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c210, c349, c391, c827, c90, c14, c655, c116, c751, c828, c707, c34, c711, c256, c253, c216, c220, c54, c308, c124, c59, c58, c327] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c349 := h 348 (by decide)
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c827 := derived827 a h
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c655 := derived655 a h
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c751 := derived751 a h
  have h9 : Entails.eval a c828 := derived828 a h
  have h10 : Entails.eval a c707 := derived707 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c711 := derived711 a h
  have h13 : Entails.eval a c256 := h 255 (by decide)
  have h14 : Entails.eval a c253 := h 252 (by decide)
  have h15 : Entails.eval a c216 := h 215 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c54 := h 53 (by decide)
  have h18 : Entails.eval a c308 := h 307 (by decide)
  have h19 : Entails.eval a c124 := h 123 (by decide)
  have h20 : Entails.eval a c59 := h 58 (by decide)
  have h21 : Entails.eval a c58 := h 57 (by decide)
  have h22 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨4, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c88, some c185, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 57) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c12, c88, c185] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c830, some c185, some c40, some c264, some c137, some c54, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 57) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c830, c185, c40, c264, c137, c54] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c830 := derived830 a h
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨26, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c14, some c90, some c830, some c116, some c727, some c117, some c533, some c831, some c25, some c4, some c202, some c316, some c149, some c436, some c66, some c322, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 57) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c14, c90, c830, c116, c727, c117, c533, c831, c25, c4, c202, c316, c149, c436, c66, c322] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c830 := derived830 a h
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c727 := derived727 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c533 := derived533 a h
  have h7 : Entails.eval a c831 := derived831 a h
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  have h12 : Entails.eval a c149 := h 148 (by decide)
  have h13 : Entails.eval a c436 := derived436 a h
  have h14 : Entails.eval a c66 := h 65 (by decide)
  have h15 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c827, some c90, some c14, some c655, some c116, some c751, some c830, some c389, some c110, some c832, some c124, some c828, some c829, some c831, some c258, some c4, some c47, some c316, some c253, some c33, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 57) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c391, c827, c90, c14, c655, c116, c751, c830, c389, c110, c832, c124, c828, c829, c831, c258, c4, c47, c316, c253, c33] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c827 := derived827 a h
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c751 := derived751 a h
  have h7 : Entails.eval a c830 := derived830 a h
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c832 := derived832 a h
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c828 := derived828 a h
  have h13 : Entails.eval a c829 := derived829 a h
  have h14 : Entails.eval a c831 := derived831 a h
  have h15 : Entails.eval a c258 := h 257 (by decide)
  have h16 : Entails.eval a c4 := h 3 (by decide)
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c316 := h 315 (by decide)
  have h19 : Entails.eval a c253 := h 252 (by decide)
  have h20 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c833, some c391, some c827, some c90, some c14, some c260, some c704, some c36, some c44, some c120, some c303, some c2, some c34, some c131, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 57) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c833, c391, c827, c90, c14, c260, c704, c36, c44, c120, c303, c2, c34, c131] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c833 := derived833 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c827 := derived827 a h
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c704 := derived704 a h
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c66, some c314, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 57) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c62, c66, c314] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c835, some c63, some c31, some c322, some c303, some c262, some c217, some c44, some c54, some c270, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 57) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c835, c63, c31, c322, c303, c262, c217, c44, c54, c270] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c835 := derived835 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c303 := h 302 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c217 := h 216 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c833, some c391, some c827, some c90, some c655, some c116, some c751, some c727, some c117, some c834, some c30, some c120, some c110, some c835, some c836, some c314, some c220, some c436, some c262, some c322, some c50, some c51, some c217, some c270, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 57) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c833, c391, c827, c90, c655, c116, c751, c727, c117, c834, c30, c120, c110, c835, c836, c314, c220, c436, c262, c322, c50, c51, c217, c270] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c833 := derived833 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c827 := derived827 a h
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c751 := derived751 a h
  have h7 : Entails.eval a c727 := derived727 a h
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c834 := derived834 a h
  have h10 : Entails.eval a c30 := h 29 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c835 := derived835 a h
  have h14 : Entails.eval a c836 := derived836 a h
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c436 := derived436 a h
  have h18 : Entails.eval a c262 := h 261 (by decide)
  have h19 : Entails.eval a c322 := h 321 (by decide)
  have h20 : Entails.eval a c50 := h 49 (by decide)
  have h21 : Entails.eval a c51 := h 50 (by decide)
  have h22 : Entails.eval a c217 := h 216 (by decide)
  have h23 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c827, some c14, some c90, some c837, some c828, some c751, some c704, some c110, some c210, some c346, some c349, some c705, some c262, some c220, some c314, some c305, some c58, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 57) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c391, c827, c14, c90, c837, c828, c751, c704, c110, c210, c346, c349, c705, c262, c220, c314, c305, c58] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c827 := derived827 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c837 := derived837 a h
  have h5 : Entails.eval a c828 := derived828 a h
  have h6 : Entails.eval a c751 := derived751 a h
  have h7 : Entails.eval a c704 := derived704 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c210 := h 209 (by decide)
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c705 := derived705 a h
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c305 := h 304 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c827, some c90, some c14, some c751, some c833, some c837, some c828, some c838, some c123, some c120, some c60, some c57, some c305, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 57) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c391, c827, c90, c14, c751, c833, c837, c828, c838, c123, c120, c60, c57, c305] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c827 := derived827 a h
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c751 := derived751 a h
  have h5 : Entails.eval a c833 := derived833 a h
  have h6 : Entails.eval a c837 := derived837 a h
  have h7 : Entails.eval a c828 := derived828 a h
  have h8 : Entails.eval a c838 := derived838 a h
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c786, some c305, some c29, some c253, some c126, some c54, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 57) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c786, c305, c29, c253, c126, c54] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c786 := derived786 a h
  have h1 : Entails.eval a c305 := h 304 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c253 := h 252 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c828, some c840, some c33, some c66, some c253, some c37, some c29, some c290, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 57) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c828, c840, c33, c66, c253, c37, c29, c290] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c828 := derived828 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c90, some c14, some c116, some c841, some c124, some c110, some c309, some c62, some c58, some c31, some c295, some c290, some c257, some c262, some c244, some c677, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 57) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c90, c14, c116, c841, c124, c110, c309, c62, c58, c31, c295, c290, c257, c262, c244, c677] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c90 := h 89 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c257 := h 256 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c244 := h 243 (by decide)
  have h15 : Entails.eval a c677 := derived677 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c751, some c827, some c14, some c90, some c839, some c312, some c842, some c727, some c36, some c8, some c260, some c139, some c34, some c325, some c295, some c65, some c38, some c120, some c110, some c63, some c309, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 57) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c655, c391, c751, c827, c14, c90, c839, c312, c842, c727, c36, c8, c260, c139, c34, c325, c295, c65, c38, c120, c110, c63, c309] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c751 := derived751 a h
  have h3 : Entails.eval a c827 := derived827 a h
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c839 := derived839 a h
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c842 := derived842 a h
  have h9 : Entails.eval a c727 := derived727 a h
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c260 := h 259 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c65 := h 64 (by decide)
  have h18 : Entails.eval a c38 := h 37 (by decide)
  have h19 : Entails.eval a c120 := h 119 (by decide)
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c63 := h 62 (by decide)
  have h22 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c436, some c63, some c314, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 57) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c436, c63, c314] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c436 := derived436 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨6, by decide⟩, true), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c727, some c116, some c110, some c117, some c392, some c835, some c844, some c303, some c103, some c99, some c385, some c384, some c373, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 57) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c727, c116, c110, c117, c392, c835, c844, c303, c103, c99, c385, c384, c373] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c727 := derived727 a h
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c392 := h 391 (by decide)
  have h5 : Entails.eval a c835 := derived835 a h
  have h6 : Entails.eval a c844 := derived844 a h
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c384 := h 383 (by decide)
  have h12 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨49, by decide⟩, true), (⟨14, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c202, some c189, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 57) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c206, c202, c189] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨33, by decide⟩, true), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c141, some c179, some c290, some c366, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 57) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c189, c141, c179, c290, c366] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c290 := h 289 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c387, some c846, some c655, some c319, some c8, some c148, some c119, some c72, some c109, some c76, some c847, some c174, some c366, some c179, some c295, some c142, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 57) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c843, c387, c846, c655, c319, c8, c148, c119, c72, c109, c76, c847, c174, c366, c179, c295, c142] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c846 := derived846 a h
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c847 := derived847 a h
  have h12 : Entails.eval a c174 := h 173 (by decide)
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c179 := h 178 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  have h16 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c62, some c91, some c68, some c299, some c328, some c87, some c39, some c66, some c262, some c227, some c213, some c323, some c69, some c141, some c209, some c126, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 57) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c34, c62, c91, c68, c299, c328, c87, c39, c66, c262, c227, c213, c323, c69, c141, c209, c126] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c299 := h 298 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  have h12 : Entails.eval a c323 := h 322 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c141 := h 140 (by decide)
  have h15 : Entails.eval a c209 := h 208 (by decide)
  have h16 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c845, some c387, some c846, some c848, some c34, some c267, some c849, some c119, some c117, some c23, some c27, some c51, some c55, some c134, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 57) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c843, c655, c845, c387, c846, c848, c34, c267, c849, c119, c117, c23, c27, c51, c55, c134] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c845 := derived845 a h
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c846 := derived846 a h
  have h5 : Entails.eval a c848 := derived848 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c849 := derived849 a h
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c55 := h 54 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c207, some c208, some c25, some c193, some c121, some c179, some c86, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 57) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c843, c655, c207, c208, c25, c193, c121, c179, c86] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c850, some c118, some c843, some c655, some c23, some c851, some c27, some c117, some c15, some c91, some c109, some c183, some c121, some c87, some c830, some c392, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 57) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c850, c118, c843, c655, c23, c851, c27, c117, c15, c91, c109, c183, c121, c87, c830, c392] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c850 := derived850 a h
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c851 := derived851 a h
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c830 := derived830 a h
  have h15 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c850, some c118, some c852, some c206, some c187, some c193, some c10, some c99, some c121, some c830, some c698, some c392, some c370, some c11, some c183, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 57) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c843, c655, c850, c118, c852, c206, c187, c193, c10, c99, c121, c830, c698, c392, c370, c11, c183] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c850 := derived850 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c852 := derived852 a h
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c187 := h 186 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c830 := derived830 a h
  have h12 : Entails.eval a c698 := derived698 a h
  have h13 : Entails.eval a c392 := h 391 (by decide)
  have h14 : Entails.eval a c370 := h 369 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨47, by decide⟩, false), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c188, some c183, some c99, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 57) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c188, c183, c99] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c188 := h 187 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c370, some c854, some c200, some c15, some c387, some c117, some c366, some c758, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 57) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c843, c655, c370, c854, c200, c15, c387, c117, c366, c758] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c854 := derived854 a h
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c387 := h 386 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c366 := h 365 (by decide)
  have h9 : Entails.eval a c758 := derived758 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨46, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c855, some c698, some c383, some c121, some c99, some c10, some c177, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 57) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c843, c855, c698, c383, c121, c99, c10, c177] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨46, by decide⟩, false), (⟨3, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c383, some c121, some c44, some c99, some c10, some c132, some c293, some c30, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c698, c383, c121, c44, c99, c10, c132, c293, c30] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c853, some c843, some c655, some c856, some c3, some c11, some c392, some c314, some c857, some c86, some c121, some c112, some c12, some c88, some c117, some c33, some c5, some c262, some c136, some c39, some c32, some c297, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c853, c843, c655, c856, c3, c11, c392, c314, c857, c86, c121, c112, c12, c88, c117, c33, c5, c262, c136, c39, c32, c297] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c853 := derived853 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c856 := derived856 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c392 := h 391 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c857 := derived857 a h
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c117 := h 116 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c262 := h 261 (by decide)
  have h18 : Entails.eval a c136 := h 135 (by decide)
  have h19 : Entails.eval a c39 := h 38 (by decide)
  have h20 : Entails.eval a c32 := h 31 (by decide)
  have h21 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c843, some c655, some c370, some c86, some c121, some c25, some c204, some c207, some c193, some c27, some c183, some c117, some c87, some c112, some c392, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c23, c843, c655, c370, c86, c121, c25, c204, c207, c193, c27, c183, c117, c87, c112, c392] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c858, some c23, some c859, some c698, some c383, some c121, some c99, some c10, some c177, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c843, c858, c23, c859, c698, c383, c121, c99, c10, c177] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c858 := derived858 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c859 := derived859 a h
  have h4 : Entails.eval a c698 := derived698 a h
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c853, some c843, some c655, some c860, some c14, some c6, some c22, some c387, some c319, some c8, some c855, some c383, some c99, some c177, some c193, some c189, some c203, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c853, c843, c655, c860, c14, c6, c22, c387, c319, c8, c855, c383, c99, c177, c193, c189, c203] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c853 := derived853 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c860 := derived860 a h
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c387 := h 386 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c855 := derived855 a h
  have h11 : Entails.eval a c383 := h 382 (by decide)
  have h12 : Entails.eval a c99 := h 98 (by decide)
  have h13 : Entails.eval a c177 := h 176 (by decide)
  have h14 : Entails.eval a c193 := h 192 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c853, some c861, some c727, some c119, some c118, some c387, some c15, some c91, some c6, some c22, some c183, some c319, some c87, some c39, some c392, some c135, some c35, some c56, some c489, some c495, some c366, some c368, some c382, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c843, c655, c853, c861, c727, c119, c118, c387, c15, c91, c6, c22, c183, c319, c87, c39, c392, c135, c35, c56, c489, c495, c366, c368, c382] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c853 := derived853 a h
  have h3 : Entails.eval a c861 := derived861 a h
  have h4 : Entails.eval a c727 := derived727 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c387 := h 386 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c392 := h 391 (by decide)
  have h17 : Entails.eval a c135 := h 134 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c489 := derived489 a h
  have h21 : Entails.eval a c495 := derived495 a h
  have h22 : Entails.eval a c366 := h 365 (by decide)
  have h23 : Entails.eval a c368 := h 367 (by decide)
  have h24 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c862, some c843, some c655, some c727, some c119, some c118, some c411, some c387, some c15, some c42, some c98, some c267, some c183, some c3, some c11, some c22, some c314, some c299, some c849, some c846, some c35, some c319, some c506, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c862, c843, c655, c727, c119, c118, c411, c387, c15, c42, c98, c267, c183, c3, c11, c22, c314, c299, c849, c846, c35, c319, c506] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c862 := derived862 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c727 := derived727 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c411 := derived411 a h
  have h7 : Entails.eval a c387 := h 386 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c314 := h 313 (by decide)
  have h17 : Entails.eval a c299 := h 298 (by decide)
  have h18 : Entails.eval a c849 := derived849 a h
  have h19 : Entails.eval a c846 := derived846 a h
  have h20 : Entails.eval a c35 := h 34 (by decide)
  have h21 : Entails.eval a c319 := h 318 (by decide)
  have h22 : Entails.eval a c506 := derived506 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨11, by decide⟩, true), (⟨46, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c90, some c22, some c387, some c846, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c843, c90, c22, c387, c846] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c846 := derived846 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c109, some c112, some c121, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c843, c655, c109, c112, c121] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c60, some c293, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c86, c60, c293] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c33, some c866, some c121, some c12, some c88, some c136, some c297, some c32, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c5, c33, c866, c121, c12, c88, c136, c297, c32] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c866 := derived866 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c863, some c862, some c843, some c23, some c3, some c11, some c314, some c392, some c864, some c865, some c117, some c33, some c262, some c867, some c39, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c863, c862, c843, c23, c3, c11, c314, c392, c864, c865, c117, c33, c262, c867, c39] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c863 := derived863 a h
  have h1 : Entails.eval a c862 := derived862 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c392 := h 391 (by decide)
  have h8 : Entails.eval a c864 := derived864 a h
  have h9 : Entails.eval a c865 := derived865 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c262 := h 261 (by decide)
  have h13 : Entails.eval a c867 := derived867 a h
  have h14 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨19, by decide⟩, false), (⟨52, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c88, some c133, some c300, some c32, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c12, c88, c133, c300, c32] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨51, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c392, some c262, some c33, some c41, some c869, some c121, some c10, some c48, some c129, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c392, c262, c33, c41, c869, c121, c10, c48, c129] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c392 := h 391 (by decide)
  have h1 : Entails.eval a c262 := h 261 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c869 := derived869 a h
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c392, some c870, some c31, some c39, some c314, some c867, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c392, c870, c31, c39, c314, c867] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c392 := h 391 (by decide)
  have h1 : Entails.eval a c870 := derived870 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c867 := derived867 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨43, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c868, some c863, some c177, some c859, some c206, some c855, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c868, c863, c177, c859, c206, c855] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c868 := derived868 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c859 := derived859 a h
  have h4 : Entails.eval a c206 := h 205 (by decide)
  have h5 : Entails.eval a c855 := derived855 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c868, some c863, some c862, some c843, some c655, some c871, some c87, some c872, some c193, some c208, some c183, some c27, some c377, some c203, some c387, some c189, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c868, c863, c862, c843, c655, c871, c87, c872, c193, c208, c183, c27, c377, c203, c387, c189] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c868 := derived868 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c862 := derived862 a h
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c871 := derived871 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c872 := derived872 a h
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c387 := h 386 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c868, some c655, some c873, some c117, some c15, some c91, some c865, some c183, some c392, some c87, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c868, c655, c873, c117, c15, c91, c865, c183, c392, c87] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c868 := derived868 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c873 := derived873 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c865 := derived865 a h
  have h7 : Entails.eval a c183 := h 182 (by decide)
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c862, some c863, some c874, some c90, some c42, some c98, some c267, some c36, some c319, some c62, some c6, some c849, some c117, some c66, some c102, some c298, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c655, c862, c863, c874, c90, c42, c98, c267, c36, c319, c62, c6, c849, c117, c66, c102, c298] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c862 := derived862 a h
  have h2 : Entails.eval a c863 := derived863 a h
  have h3 : Entails.eval a c874 := derived874 a h
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c319 := h 318 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c849 := derived849 a h
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c875, some c843, some c655, some c89, some c114, some c13, some c387, some c683, some c182, some c119, some c23, some c22, some c846, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c875, c843, c655, c89, c114, c13, c387, c683, c182, c119, c23, c22, c846] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c875 := derived875 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c387 := h 386 (by decide)
  have h7 : Entails.eval a c683 := derived683 a h
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c846 := derived846 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c875, some c843, some c655, some c876, some c117, some c15, some c91, some c109, some c116, some c183, some c385, some c387, some c3, some c22, some c369, some c299, some c846, some c293, some c68, some c23, some c319, some c848, some c148, some c42, some c76, some c142, some c210, some c131, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c875, c843, c655, c876, c117, c15, c91, c109, c116, c183, c385, c387, c3, c22, c369, c299, c846, c293, c68, c23, c319, c848, c148, c42, c76, c142, c210, c131] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c875 := derived875 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c876 := derived876 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c369 := h 368 (by decide)
  have h15 : Entails.eval a c299 := h 298 (by decide)
  have h16 : Entails.eval a c846 := derived846 a h
  have h17 : Entails.eval a c293 := h 292 (by decide)
  have h18 : Entails.eval a c68 := h 67 (by decide)
  have h19 : Entails.eval a c23 := h 22 (by decide)
  have h20 : Entails.eval a c319 := h 318 (by decide)
  have h21 : Entails.eval a c848 := derived848 a h
  have h22 : Entails.eval a c148 := h 147 (by decide)
  have h23 : Entails.eval a c42 := h 41 (by decide)
  have h24 : Entails.eval a c76 := h 75 (by decide)
  have h25 : Entails.eval a c142 := h 141 (by decide)
  have h26 : Entails.eval a c210 := h 209 (by decide)
  have h27 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c15, some c91, some c109, some c865, some c183, some c121, some c3, some c11, some c299, some c313, some c64, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c843, c655, c15, c91, c109, c865, c183, c121, c3, c11, c299, c313, c64] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c865 := derived865 a h
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c875, some c843, some c655, some c877, some c878, some c117, some c89, some c13, some c108, some c385, some c384, some c182, some c121, some c373, some c40, some c3, some c11, some c298, some c313, some c33, some c4, some c136, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c875, c843, c655, c877, c878, c117, c89, c13, c108, c385, c384, c182, c121, c373, c40, c3, c11, c298, c313, c33, c4, c136] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c875 := derived875 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c877 := derived877 a h
  have h4 : Entails.eval a c878 := derived878 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c182 := h 181 (by decide)
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c373 := h 372 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c298 := h 297 (by decide)
  have h18 : Entails.eval a c313 := h 312 (by decide)
  have h19 : Entails.eval a c33 := h 32 (by decide)
  have h20 : Entails.eval a c4 := h 3 (by decide)
  have h21 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c3, some c843, some c655, some c370, some c857, some c180, some c377, some c193, some c387, some c201, some c189, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c23, c3, c843, c655, c370, c857, c180, c377, c193, c387, c201, c189] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c857 := derived857 a h
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c387 := h 386 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c23, some c880, some c758, some c188, some c193, some c180, some c533, some c366, some c200, some c387, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c843, c655, c23, c880, c758, c188, c193, c180, c533, c366, c200, c387] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c880 := derived880 a h
  have h4 : Entails.eval a c758 := derived758 a h
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c533 := derived533 a h
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨19, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c89, some c13, some c108, some c121, some c881, some c207, some c134, some c12, some c4, some c33, some c261, some c300, some c40, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c843, c89, c13, c108, c121, c881, c207, c134, c12, c4, c33, c261, c300, c40] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c881 := derived881 a h
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c879, some c39, some c87, some c875, some c843, some c655, some c118, some c99, some c882, some c117, some c15, some c91, some c109, some c865, some c188, some c121, some c261, some c23, some c52, some c135, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c879, c39, c87, c875, c843, c655, c118, c99, c882, c117, c15, c91, c109, c865, c188, c121, c261, c23, c52, c135] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c879 := derived879 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c875 := derived875 a h
  have h4 : Entails.eval a c843 := derived843 a h
  have h5 : Entails.eval a c655 := derived655 a h
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c882 := derived882 a h
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c865 := derived865 a h
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c121 := h 120 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c23 := h 22 (by decide)
  have h18 : Entails.eval a c52 := h 51 (by decide)
  have h19 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨31, by decide⟩, false), (⟨47, by decide⟩, false), (⟨43, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c36, some c304, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c99, c36, c304] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨49, by decide⟩, true), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c379, some c366, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c383, c379, c366] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨49, by decide⟩, true), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c366, some c378, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c369, c366, c378] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c879, some c883, some c98, some c843, some c875, some c655, some c91, some c116, some c387, some c886, some c382, some c885, some c15, some c39, some c87, some c208, some c135, some c192, some c35, some c56, some c267, some c884, some c179, some c6, some c249, some c319, some c261, some c489, some c368, some c495, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c879, c883, c98, c843, c875, c655, c91, c116, c387, c886, c382, c885, c15, c39, c87, c208, c135, c192, c35, c56, c267, c884, c179, c6, c249, c319, c261, c489, c368, c495] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c879 := derived879 a h
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c875 := derived875 a h
  have h5 : Entails.eval a c655 := derived655 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c886 := derived886 a h
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c885 := derived885 a h
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  have h16 : Entails.eval a c135 := h 134 (by decide)
  have h17 : Entails.eval a c192 := h 191 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c267 := h 266 (by decide)
  have h21 : Entails.eval a c884 := derived884 a h
  have h22 : Entails.eval a c179 := h 178 (by decide)
  have h23 : Entails.eval a c6 := h 5 (by decide)
  have h24 : Entails.eval a c249 := h 248 (by decide)
  have h25 : Entails.eval a c319 := h 318 (by decide)
  have h26 : Entails.eval a c261 := h 260 (by decide)
  have h27 : Entails.eval a c489 := derived489 a h
  have h28 : Entails.eval a c368 := h 367 (by decide)
  have h29 : Entails.eval a c495 := derived495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c879, some c883, some c98, some c875, some c843, some c655, some c15, some c91, some c116, some c387, some c886, some c887, some c22, some c179, some c192, some c189, some c201, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c879, c883, c98, c875, c843, c655, c15, c91, c116, c387, c886, c887, c22, c179, c192, c189, c201] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c879 := derived879 a h
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c875 := derived875 a h
  have h4 : Entails.eval a c843 := derived843 a h
  have h5 : Entails.eval a c655 := derived655 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c387 := h 386 (by decide)
  have h10 : Entails.eval a c886 := derived886 a h
  have h11 : Entails.eval a c887 := derived887 a h
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c192 := h 191 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c875, some c879, some c883, some c98, some c888, some c119, some c117, some c99, some c114, some c885, some c387, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c843, c875, c879, c883, c98, c888, c119, c117, c99, c114, c885, c387] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c875 := derived875 a h
  have h2 : Entails.eval a c879 := derived879 a h
  have h3 : Entails.eval a c883 := derived883 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c888 := derived888 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c885 := derived885 a h
  have h11 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c655, some c370, some c886, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c843, c655, c370, c886] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c886 := derived886 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨13, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c55, some c53, some c136, some c265, some c12, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c267, c55, c53, c136, c265, c12] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c891, some c42, some c55, some c44, some c36, some c53, some c136, some c319, some c296, some c25, some c214, some c180, some c75, some c142, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c698, c891, c42, c55, c44, c36, c53, c136, c319, c296, c25, c214, c180, c75, c142] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c891 := derived891 a h
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c214 := h 213 (by decide)
  have h12 : Entails.eval a c180 := h 179 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c42, some c136, some c275, some c25, some c12, some c4, some c246, some c846, some c317, some c384, some c182, some c214, some c101, some c514, some c75, some c180, some c142, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c698, c42, c136, c275, c25, c12, c4, c246, c846, c317, c384, c182, c214, c101, c514, c75, c180, c142] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  have h8 : Entails.eval a c846 := derived846 a h
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c182 := h 181 (by decide)
  have h12 : Entails.eval a c214 := h 213 (by decide)
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c514 := derived514 a h
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c180 := h 179 (by decide)
  have h17 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived893

end CochromaticTwenty.Certificates.B16_1_2
