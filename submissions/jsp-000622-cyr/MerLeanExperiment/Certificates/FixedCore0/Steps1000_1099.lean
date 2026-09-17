import MerLeanExperiment.Certificates.FixedCore0.Steps0900_0999

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8551 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8551 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8538, some c8496, some c8380, some c8549, some c16, some c47, some c8550, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8551 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8551 : lratChecker f8551 p8551 = .success := by decide +kernel
theorem unsat8551 : Unsatisfiable (PosFin 65) f8551 := by
  apply lratCheckerSound f8551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8551
  · intro a ha; simp [p8551] at ha; subst a; trivial
  · exact checked8551
theorem derived8551 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8551 := by
  apply localUnsat_implies_entails f8551 [c8538, c8496, c8380, c8549, c16, c47, c8550] c8551 unsat8551 (by rfl) a
  have h0 : Entails.eval a c8538 := derived8538 a h
  have h1 : Entails.eval a c8496 := derived8496 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c8549 := derived8549 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c8550 := derived8550 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8552 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨32, by decide⟩, false), (⟨63, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8552 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5653, some c5729, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p8552 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8552 : lratChecker f8552 p8552 = .success := by decide +kernel
theorem unsat8552 : Unsatisfiable (PosFin 65) f8552 := by
  apply lratCheckerSound f8552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8552
  · intro a ha; simp [p8552] at ha; subst a; trivial
  · exact checked8552
theorem derived8552 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8552 := by
  apply localUnsat_implies_entails f8552 [c5653, c5729] c8552 unsat8552 (by rfl) a
  have h0 : Entails.eval a c5653 := h 5652 (by decide)
  have h1 : Entails.eval a c5729 := h 5728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8553 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨63, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8553 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8552, some c5735, some c5659, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p8553 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8553 : lratChecker f8553 p8553 = .success := by decide +kernel
theorem unsat8553 : Unsatisfiable (PosFin 65) f8553 := by
  apply lratCheckerSound f8553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8553
  · intro a ha; simp [p8553] at ha; subst a; trivial
  · exact checked8553
theorem derived8553 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8553 := by
  apply localUnsat_implies_entails f8553 [c8552, c5735, c5659] c8553 unsat8553 (by rfl) a
  have h0 : Entails.eval a c8552 := derived8552 a h
  have h1 : Entails.eval a c5735 := h 5734 (by decide)
  have h2 : Entails.eval a c5659 := h 5658 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8554 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8554 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1440, some c5708, some c4882, some c4876, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8554 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8554 : lratChecker f8554 p8554 = .success := by decide +kernel
theorem unsat8554 : Unsatisfiable (PosFin 65) f8554 := by
  apply lratCheckerSound f8554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8554
  · intro a ha; simp [p8554] at ha; subst a; trivial
  · exact checked8554
theorem derived8554 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8554 := by
  apply localUnsat_implies_entails f8554 [c1440, c5708, c4882, c4876] c8554 unsat8554 (by rfl) a
  have h0 : Entails.eval a c1440 := h 1439 (by decide)
  have h1 : Entails.eval a c5708 := h 5707 (by decide)
  have h2 : Entails.eval a c4882 := h 4881 (by decide)
  have h3 : Entails.eval a c4876 := h 4875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8555 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false), (⟨63, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8555 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8553, some c8554, some c6074, some c5789, some c6239, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8555 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8555 : lratChecker f8555 p8555 = .success := by decide +kernel
theorem unsat8555 : Unsatisfiable (PosFin 65) f8555 := by
  apply lratCheckerSound f8555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8555
  · intro a ha; simp [p8555] at ha; subst a; trivial
  · exact checked8555
theorem derived8555 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8555 := by
  apply localUnsat_implies_entails f8555 [c8553, c8554, c6074, c5789, c6239] c8555 unsat8555 (by rfl) a
  have h0 : Entails.eval a c8553 := derived8553 a h
  have h1 : Entails.eval a c8554 := derived8554 a h
  have h2 : Entails.eval a c6074 := h 6073 (by decide)
  have h3 : Entails.eval a c5789 := h 5788 (by decide)
  have h4 : Entails.eval a c6239 := h 6238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8556 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨21, by decide⟩, false), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8556 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1440, some c5708, some c4867, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8556 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8556 : lratChecker f8556 p8556 = .success := by decide +kernel
theorem unsat8556 : Unsatisfiable (PosFin 65) f8556 := by
  apply lratCheckerSound f8556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8556
  · intro a ha; simp [p8556] at ha; subst a; trivial
  · exact checked8556
theorem derived8556 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8556 := by
  apply localUnsat_implies_entails f8556 [c1440, c5708, c4867] c8556 unsat8556 (by rfl) a
  have h0 : Entails.eval a c1440 := h 1439 (by decide)
  have h1 : Entails.eval a c5708 := h 5707 (by decide)
  have h2 : Entails.eval a c4867 := h 4866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8557 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨54, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8557 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8484, some c8551, some c8538, some c8496, some c8523, some c8421, some c8539, some c8553, some c8544, some c8555, some c8556, some c5752, some c6033, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8557 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8557 : lratChecker f8557 p8557 = .success := by decide +kernel
theorem unsat8557 : Unsatisfiable (PosFin 65) f8557 := by
  apply lratCheckerSound f8557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8557
  · intro a ha; simp [p8557] at ha; subst a; trivial
  · exact checked8557
theorem derived8557 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8557 := by
  apply localUnsat_implies_entails f8557 [c8484, c8551, c8538, c8496, c8523, c8421, c8539, c8553, c8544, c8555, c8556, c5752, c6033] c8557 unsat8557 (by rfl) a
  have h0 : Entails.eval a c8484 := derived8484 a h
  have h1 : Entails.eval a c8551 := derived8551 a h
  have h2 : Entails.eval a c8538 := derived8538 a h
  have h3 : Entails.eval a c8496 := derived8496 a h
  have h4 : Entails.eval a c8523 := derived8523 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8539 := derived8539 a h
  have h7 : Entails.eval a c8553 := derived8553 a h
  have h8 : Entails.eval a c8544 := derived8544 a h
  have h9 : Entails.eval a c8555 := derived8555 a h
  have h10 : Entails.eval a c8556 := derived8556 a h
  have h11 : Entails.eval a c5752 := h 5751 (by decide)
  have h12 : Entails.eval a c6033 := h 6032 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8558 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨63, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8558 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8546, some c8553, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p8558 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8558 : lratChecker f8558 p8558 = .success := by decide +kernel
theorem unsat8558 : Unsatisfiable (PosFin 65) f8558 := by
  apply lratCheckerSound f8558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8558
  · intro a ha; simp [p8558] at ha; subst a; trivial
  · exact checked8558
theorem derived8558 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8558 := by
  apply localUnsat_implies_entails f8558 [c8546, c8553] c8558 unsat8558 (by rfl) a
  have h0 : Entails.eval a c8546 := derived8546 a h
  have h1 : Entails.eval a c8553 := derived8553 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8559 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨63, by decide⟩, true), (⟨56, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8559 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8558, some c5812, some c5826, some c5818, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p8559 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8559 : lratChecker f8559 p8559 = .success := by decide +kernel
theorem unsat8559 : Unsatisfiable (PosFin 65) f8559 := by
  apply lratCheckerSound f8559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8559
  · intro a ha; simp [p8559] at ha; subst a; trivial
  · exact checked8559
theorem derived8559 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8559 := by
  apply localUnsat_implies_entails f8559 [c8558, c5812, c5826, c5818] c8559 unsat8559 (by rfl) a
  have h0 : Entails.eval a c8558 := derived8558 a h
  have h1 : Entails.eval a c5812 := h 5811 (by decide)
  have h2 : Entails.eval a c5826 := h 5825 (by decide)
  have h3 : Entails.eval a c5818 := h 5817 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8560 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8560 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8551, some c8538, some c8496, some c8523, some c8484, some c8557, some c8559, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8560 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8560 : lratChecker f8560 p8560 = .success := by decide +kernel
theorem unsat8560 : Unsatisfiable (PosFin 65) f8560 := by
  apply lratCheckerSound f8560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8560
  · intro a ha; simp [p8560] at ha; subst a; trivial
  · exact checked8560
theorem derived8560 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8560 := by
  apply localUnsat_implies_entails f8560 [c8551, c8538, c8496, c8523, c8484, c8557, c8559] c8560 unsat8560 (by rfl) a
  have h0 : Entails.eval a c8551 := derived8551 a h
  have h1 : Entails.eval a c8538 := derived8538 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c8523 := derived8523 a h
  have h4 : Entails.eval a c8484 := derived8484 a h
  have h5 : Entails.eval a c8557 := derived8557 a h
  have h6 : Entails.eval a c8559 := derived8559 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8561 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8561 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c380, some c386, some c387, some c385, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true))]
def p8561 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8561 : lratChecker f8561 p8561 = .success := by decide +kernel
theorem unsat8561 : Unsatisfiable (PosFin 65) f8561 := by
  apply lratCheckerSound f8561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8561
  · intro a ha; simp [p8561] at ha; subst a; trivial
  · exact checked8561
theorem derived8561 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8561 := by
  apply localUnsat_implies_entails f8561 [c380, c386, c387, c385] c8561 unsat8561 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c386 := h 385 (by decide)
  have h2 : Entails.eval a c387 := h 386 (by decide)
  have h3 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8562 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8562 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8538, some c8496, some c8551, some c8560, some c16, some c5726, some c8550, some c8561, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8562 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8562 : lratChecker f8562 p8562 = .success := by decide +kernel
theorem unsat8562 : Unsatisfiable (PosFin 65) f8562 := by
  apply lratCheckerSound f8562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8562
  · intro a ha; simp [p8562] at ha; subst a; trivial
  · exact checked8562
theorem derived8562 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8562 := by
  apply localUnsat_implies_entails f8562 [c8380, c8538, c8496, c8551, c8560, c16, c5726, c8550, c8561] c8562 unsat8562 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8538 := derived8538 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c8551 := derived8551 a h
  have h4 : Entails.eval a c8560 := derived8560 a h
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c5726 := h 5725 (by decide)
  have h7 : Entails.eval a c8550 := derived8550 a h
  have h8 : Entails.eval a c8561 := derived8561 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8563 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8563 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8524, some c8526, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8563 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8563 : lratChecker f8563 p8563 = .success := by decide +kernel
theorem unsat8563 : Unsatisfiable (PosFin 65) f8563 := by
  apply lratCheckerSound f8563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8563
  · intro a ha; simp [p8563] at ha; subst a; trivial
  · exact checked8563
theorem derived8563 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8563 := by
  apply localUnsat_implies_entails f8563 [c8380, c8524, c8526] c8563 unsat8563 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8524 := derived8524 a h
  have h2 : Entails.eval a c8526 := derived8526 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8564 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8564 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8562, some c8523, some c8438, some c8435, some c8436, some c690, some c692, some c675, some c667, some c703, some c655, some c698, some c671, some c8563, some c571, some c621, some c5858, some c5304, some c5503, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8564 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8564 : lratChecker f8564 p8564 = .success := by decide +kernel
theorem unsat8564 : Unsatisfiable (PosFin 65) f8564 := by
  apply lratCheckerSound f8564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8564
  · intro a ha; simp [p8564] at ha; subst a; trivial
  · exact checked8564
theorem derived8564 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8564 := by
  apply localUnsat_implies_entails f8564 [c8562, c8523, c8438, c8435, c8436, c690, c692, c675, c667, c703, c655, c698, c671, c8563, c571, c621, c5858, c5304, c5503] c8564 unsat8564 (by rfl) a
  have h0 : Entails.eval a c8562 := derived8562 a h
  have h1 : Entails.eval a c8523 := derived8523 a h
  have h2 : Entails.eval a c8438 := derived8438 a h
  have h3 : Entails.eval a c8435 := derived8435 a h
  have h4 : Entails.eval a c8436 := derived8436 a h
  have h5 : Entails.eval a c690 := h 689 (by decide)
  have h6 : Entails.eval a c692 := h 691 (by decide)
  have h7 : Entails.eval a c675 := h 674 (by decide)
  have h8 : Entails.eval a c667 := h 666 (by decide)
  have h9 : Entails.eval a c703 := h 702 (by decide)
  have h10 : Entails.eval a c655 := h 654 (by decide)
  have h11 : Entails.eval a c698 := h 697 (by decide)
  have h12 : Entails.eval a c671 := h 670 (by decide)
  have h13 : Entails.eval a c8563 := derived8563 a h
  have h14 : Entails.eval a c571 := h 570 (by decide)
  have h15 : Entails.eval a c621 := h 620 (by decide)
  have h16 : Entails.eval a c5858 := h 5857 (by decide)
  have h17 : Entails.eval a c5304 := h 5303 (by decide)
  have h18 : Entails.eval a c5503 := h 5502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8565 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8565 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5946, some c5969, some c5664, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8565 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8565 : lratChecker f8565 p8565 = .success := by decide +kernel
theorem unsat8565 : Unsatisfiable (PosFin 65) f8565 := by
  apply lratCheckerSound f8565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8565
  · intro a ha; simp [p8565] at ha; subst a; trivial
  · exact checked8565
theorem derived8565 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8565 := by
  apply localUnsat_implies_entails f8565 [c5946, c5969, c5664] c8565 unsat8565 (by rfl) a
  have h0 : Entails.eval a c5946 := h 5945 (by decide)
  have h1 : Entails.eval a c5969 := h 5968 (by decide)
  have h2 : Entails.eval a c5664 := h 5663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8566 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8566 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8486, some c4895, some c5966, some c5944, some c917, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8566 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8566 : lratChecker f8566 p8566 = .success := by decide +kernel
theorem unsat8566 : Unsatisfiable (PosFin 65) f8566 := by
  apply lratCheckerSound f8566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8566
  · intro a ha; simp [p8566] at ha; subst a; trivial
  · exact checked8566
theorem derived8566 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8566 := by
  apply localUnsat_implies_entails f8566 [c8380, c8486, c4895, c5966, c5944, c917] c8566 unsat8566 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8486 := derived8486 a h
  have h2 : Entails.eval a c4895 := h 4894 (by decide)
  have h3 : Entails.eval a c5966 := h 5965 (by decide)
  have h4 : Entails.eval a c5944 := h 5943 (by decide)
  have h5 : Entails.eval a c917 := h 916 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8567 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8567 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8565, some c8566, some c8531, some c8528, some c8534, some c5764, some c5766, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8567 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8567 : lratChecker f8567 p8567 = .success := by decide +kernel
theorem unsat8567 : Unsatisfiable (PosFin 65) f8567 := by
  apply lratCheckerSound f8567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8567
  · intro a ha; simp [p8567] at ha; subst a; trivial
  · exact checked8567
theorem derived8567 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8567 := by
  apply localUnsat_implies_entails f8567 [c8380, c8565, c8566, c8531, c8528, c8534, c5764, c5766] c8567 unsat8567 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8565 := derived8565 a h
  have h2 : Entails.eval a c8566 := derived8566 a h
  have h3 : Entails.eval a c8531 := derived8531 a h
  have h4 : Entails.eval a c8528 := derived8528 a h
  have h5 : Entails.eval a c8534 := derived8534 a h
  have h6 : Entails.eval a c5764 := h 5763 (by decide)
  have h7 : Entails.eval a c5766 := h 5765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8568 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8568 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8565, some c8567, some c1446, some c4922, some c5984, some c5960, some c917, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8568 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8568 : lratChecker f8568 p8568 = .success := by decide +kernel
theorem unsat8568 : Unsatisfiable (PosFin 65) f8568 := by
  apply lratCheckerSound f8568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8568
  · intro a ha; simp [p8568] at ha; subst a; trivial
  · exact checked8568
theorem derived8568 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8568 := by
  apply localUnsat_implies_entails f8568 [c8380, c8565, c8567, c1446, c4922, c5984, c5960, c917] c8568 unsat8568 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8565 := derived8565 a h
  have h2 : Entails.eval a c8567 := derived8567 a h
  have h3 : Entails.eval a c1446 := h 1445 (by decide)
  have h4 : Entails.eval a c4922 := h 4921 (by decide)
  have h5 : Entails.eval a c5984 := h 5983 (by decide)
  have h6 : Entails.eval a c5960 := h 5959 (by decide)
  have h7 : Entails.eval a c917 := h 916 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8569 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨29, by decide⟩, true), (⟨20, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8569 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8532, some c918, some c922, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8569 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8569 : lratChecker f8569 p8569 = .success := by decide +kernel
theorem unsat8569 : Unsatisfiable (PosFin 65) f8569 := by
  apply lratCheckerSound f8569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8569
  · intro a ha; simp [p8569] at ha; subst a; trivial
  · exact checked8569
theorem derived8569 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8569 := by
  apply localUnsat_implies_entails f8569 [c8532, c918, c922] c8569 unsat8569 (by rfl) a
  have h0 : Entails.eval a c8532 := derived8532 a h
  have h1 : Entails.eval a c918 := h 917 (by decide)
  have h2 : Entails.eval a c922 := h 921 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8570 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨20, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8570 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8569, some c1407, some c915, some c4877, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8570 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8570 : lratChecker f8570 p8570 = .success := by decide +kernel
theorem unsat8570 : Unsatisfiable (PosFin 65) f8570 := by
  apply lratCheckerSound f8570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8570
  · intro a ha; simp [p8570] at ha; subst a; trivial
  · exact checked8570
theorem derived8570 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8570 := by
  apply localUnsat_implies_entails f8570 [c8569, c1407, c915, c4877] c8570 unsat8570 (by rfl) a
  have h0 : Entails.eval a c8569 := derived8569 a h
  have h1 : Entails.eval a c1407 := h 1406 (by decide)
  have h2 : Entails.eval a c915 := h 914 (by decide)
  have h3 : Entails.eval a c4877 := h 4876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8571 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8571 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8568, some c8570, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8571 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8571 : lratChecker f8571 p8571 = .success := by decide +kernel
theorem unsat8571 : Unsatisfiable (PosFin 65) f8571 := by
  apply lratCheckerSound f8571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8571
  · intro a ha; simp [p8571] at ha; subst a; trivial
  · exact checked8571
theorem derived8571 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8571 := by
  apply localUnsat_implies_entails f8571 [c8568, c8570] c8571 unsat8571 (by rfl) a
  have h0 : Entails.eval a c8568 := derived8568 a h
  have h1 : Entails.eval a c8570 := derived8570 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8572 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨49, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8572 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5741, some c5744, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p8572 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8572 : lratChecker f8572 p8572 = .success := by decide +kernel
theorem unsat8572 : Unsatisfiable (PosFin 65) f8572 := by
  apply lratCheckerSound f8572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8572
  · intro a ha; simp [p8572] at ha; subst a; trivial
  · exact checked8572
theorem derived8572 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8572 := by
  apply localUnsat_implies_entails f8572 [c5741, c5744] c8572 unsat8572 (by rfl) a
  have h0 : Entails.eval a c5741 := h 5740 (by decide)
  have h1 : Entails.eval a c5744 := h 5743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8573 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨54, by decide⟩, false), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8573 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8572, some c5576, some c158, some c6266, some c5357, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8573 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8573 : lratChecker f8573 p8573 = .success := by decide +kernel
theorem unsat8573 : Unsatisfiable (PosFin 65) f8573 := by
  apply lratCheckerSound f8573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8573
  · intro a ha; simp [p8573] at ha; subst a; trivial
  · exact checked8573
theorem derived8573 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8573 := by
  apply localUnsat_implies_entails f8573 [c8572, c5576, c158, c6266, c5357] c8573 unsat8573 (by rfl) a
  have h0 : Entails.eval a c8572 := derived8572 a h
  have h1 : Entails.eval a c5576 := h 5575 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c6266 := h 6265 (by decide)
  have h4 : Entails.eval a c5357 := h 5356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8574 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8574 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8528, some c8534, some c937, some c1409, some c4888, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8574 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8574 : lratChecker f8574 p8574 = .success := by decide +kernel
theorem unsat8574 : Unsatisfiable (PosFin 65) f8574 := by
  apply lratCheckerSound f8574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8574
  · intro a ha; simp [p8574] at ha; subst a; trivial
  · exact checked8574
theorem derived8574 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8574 := by
  apply localUnsat_implies_entails f8574 [c8528, c8534, c937, c1409, c4888] c8574 unsat8574 (by rfl) a
  have h0 : Entails.eval a c8528 := derived8528 a h
  have h1 : Entails.eval a c8534 := derived8534 a h
  have h2 : Entails.eval a c937 := h 936 (by decide)
  have h3 : Entails.eval a c1409 := h 1408 (by decide)
  have h4 : Entails.eval a c4888 := h 4887 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8575 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8575 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8574, some c8572, some c8573, some c5573, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8575 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8575 : lratChecker f8575 p8575 = .success := by decide +kernel
theorem unsat8575 : Unsatisfiable (PosFin 65) f8575 := by
  apply lratCheckerSound f8575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8575
  · intro a ha; simp [p8575] at ha; subst a; trivial
  · exact checked8575
theorem derived8575 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8575 := by
  apply localUnsat_implies_entails f8575 [c8574, c8572, c8573, c5573] c8575 unsat8575 (by rfl) a
  have h0 : Entails.eval a c8574 := derived8574 a h
  have h1 : Entails.eval a c8572 := derived8572 a h
  have h2 : Entails.eval a c8573 := derived8573 a h
  have h3 : Entails.eval a c5573 := h 5572 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8576 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8576 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5573, some c5576, some c158, some c5364, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8576 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8576 : lratChecker f8576 p8576 = .success := by decide +kernel
theorem unsat8576 : Unsatisfiable (PosFin 65) f8576 := by
  apply lratCheckerSound f8576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8576
  · intro a ha; simp [p8576] at ha; subst a; trivial
  · exact checked8576
theorem derived8576 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8576 := by
  apply localUnsat_implies_entails f8576 [c5573, c5576, c158, c5364] c8576 unsat8576 (by rfl) a
  have h0 : Entails.eval a c5573 := h 5572 (by decide)
  have h1 : Entails.eval a c5576 := h 5575 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c5364 := h 5363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8577 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8577 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8576, some c8572, some c8528, some c8534, some c5747, some c5764, some c5766, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8577 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8577 : lratChecker f8577 p8577 = .success := by decide +kernel
theorem unsat8577 : Unsatisfiable (PosFin 65) f8577 := by
  apply lratCheckerSound f8577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8577
  · intro a ha; simp [p8577] at ha; subst a; trivial
  · exact checked8577
theorem derived8577 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8577 := by
  apply localUnsat_implies_entails f8577 [c8576, c8572, c8528, c8534, c5747, c5764, c5766] c8577 unsat8577 (by rfl) a
  have h0 : Entails.eval a c8576 := derived8576 a h
  have h1 : Entails.eval a c8572 := derived8572 a h
  have h2 : Entails.eval a c8528 := derived8528 a h
  have h3 : Entails.eval a c8534 := derived8534 a h
  have h4 : Entails.eval a c5747 := h 5746 (by decide)
  have h5 : Entails.eval a c5764 := h 5763 (by decide)
  have h6 : Entails.eval a c5766 := h 5765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8578 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8578 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8575, some c8577, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8578 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8578 : lratChecker f8578 p8578 = .success := by decide +kernel
theorem unsat8578 : Unsatisfiable (PosFin 65) f8578 := by
  apply lratCheckerSound f8578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8578
  · intro a ha; simp [p8578] at ha; subst a; trivial
  · exact checked8578
theorem derived8578 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8578 := by
  apply localUnsat_implies_entails f8578 [c8575, c8577] c8578 unsat8578 (by rfl) a
  have h0 : Entails.eval a c8575 := derived8575 a h
  have h1 : Entails.eval a c8577 := derived8577 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8579 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8579 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8562, some c8523, some c8380, some c8421, some c8564, some c8571, some c8578, some c8486, some c4896, some c2734, some c5593, some c4719, some c5761, some c914, some c904, some c926, some c920, some c878, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8579 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8579 : lratChecker f8579 p8579 = .success := by decide +kernel
theorem unsat8579 : Unsatisfiable (PosFin 65) f8579 := by
  apply lratCheckerSound f8579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8579
  · intro a ha; simp [p8579] at ha; subst a; trivial
  · exact checked8579
theorem derived8579 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8579 := by
  apply localUnsat_implies_entails f8579 [c8562, c8523, c8380, c8421, c8564, c8571, c8578, c8486, c4896, c2734, c5593, c4719, c5761, c914, c904, c926, c920, c878] c8579 unsat8579 (by rfl) a
  have h0 : Entails.eval a c8562 := derived8562 a h
  have h1 : Entails.eval a c8523 := derived8523 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8564 := derived8564 a h
  have h5 : Entails.eval a c8571 := derived8571 a h
  have h6 : Entails.eval a c8578 := derived8578 a h
  have h7 : Entails.eval a c8486 := derived8486 a h
  have h8 : Entails.eval a c4896 := h 4895 (by decide)
  have h9 : Entails.eval a c2734 := h 2733 (by decide)
  have h10 : Entails.eval a c5593 := h 5592 (by decide)
  have h11 : Entails.eval a c4719 := h 4718 (by decide)
  have h12 : Entails.eval a c5761 := h 5760 (by decide)
  have h13 : Entails.eval a c914 := h 913 (by decide)
  have h14 : Entails.eval a c904 := h 903 (by decide)
  have h15 : Entails.eval a c926 := h 925 (by decide)
  have h16 : Entails.eval a c920 := h 919 (by decide)
  have h17 : Entails.eval a c878 := h 877 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8580 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8580 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c662, some c8506, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8580 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8580 : lratChecker f8580 p8580 = .success := by decide +kernel
theorem unsat8580 : Unsatisfiable (PosFin 65) f8580 := by
  apply lratCheckerSound f8580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8580
  · intro a ha; simp [p8580] at ha; subst a; trivial
  · exact checked8580
theorem derived8580 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8580 := by
  apply localUnsat_implies_entails f8580 [c662, c8506] c8580 unsat8580 (by rfl) a
  have h0 : Entails.eval a c662 := h 661 (by decide)
  have h1 : Entails.eval a c8506 := derived8506 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8581 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨22, by decide⟩, true), (⟨11, by decide⟩, true), (⟨32, by decide⟩, true), (⟨49, by decide⟩, false), (⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8581 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4871, some c4862, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8581 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8581 : lratChecker f8581 p8581 = .success := by decide +kernel
theorem unsat8581 : Unsatisfiable (PosFin 65) f8581 := by
  apply lratCheckerSound f8581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8581
  · intro a ha; simp [p8581] at ha; subst a; trivial
  · exact checked8581
theorem derived8581 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8581 := by
  apply localUnsat_implies_entails f8581 [c4871, c4862] c8581 unsat8581 (by rfl) a
  have h0 : Entails.eval a c4871 := h 4870 (by decide)
  have h1 : Entails.eval a c4862 := h 4861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8582 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8582 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8580, some c8505, some c675, some c667, some c682, some c685, some c661, some c698, some c688, some c8581, some c907, some c903, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8582 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8582 : lratChecker f8582 p8582 = .success := by decide +kernel
theorem unsat8582 : Unsatisfiable (PosFin 65) f8582 := by
  apply lratCheckerSound f8582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8582
  · intro a ha; simp [p8582] at ha; subst a; trivial
  · exact checked8582
theorem derived8582 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8582 := by
  apply localUnsat_implies_entails f8582 [c8580, c8505, c675, c667, c682, c685, c661, c698, c688, c8581, c907, c903] c8582 unsat8582 (by rfl) a
  have h0 : Entails.eval a c8580 := derived8580 a h
  have h1 : Entails.eval a c8505 := derived8505 a h
  have h2 : Entails.eval a c675 := h 674 (by decide)
  have h3 : Entails.eval a c667 := h 666 (by decide)
  have h4 : Entails.eval a c682 := h 681 (by decide)
  have h5 : Entails.eval a c685 := h 684 (by decide)
  have h6 : Entails.eval a c661 := h 660 (by decide)
  have h7 : Entails.eval a c698 := h 697 (by decide)
  have h8 : Entails.eval a c688 := h 687 (by decide)
  have h9 : Entails.eval a c8581 := derived8581 a h
  have h10 : Entails.eval a c907 := h 906 (by decide)
  have h11 : Entails.eval a c903 := h 902 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8583 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8583 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c676, some c677, some c661, some c691, some c698, some c657, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8583 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8583 : lratChecker f8583 p8583 = .success := by decide +kernel
theorem unsat8583 : Unsatisfiable (PosFin 65) f8583 := by
  apply lratCheckerSound f8583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8583
  · intro a ha; simp [p8583] at ha; subst a; trivial
  · exact checked8583
theorem derived8583 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8583 := by
  apply localUnsat_implies_entails f8583 [c676, c677, c661, c691, c698, c657] c8583 unsat8583 (by rfl) a
  have h0 : Entails.eval a c676 := h 675 (by decide)
  have h1 : Entails.eval a c677 := h 676 (by decide)
  have h2 : Entails.eval a c661 := h 660 (by decide)
  have h3 : Entails.eval a c691 := h 690 (by decide)
  have h4 : Entails.eval a c698 := h 697 (by decide)
  have h5 : Entails.eval a c657 := h 656 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8584 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8584 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8579, some c8580, some c8562, some c8523, some c8380, some c8421, some c8486, some c8582, some c8583, some c692, some c685, some c697, some c8510, some c8511, some c8532, some c237, some c235, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8584 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8584 : lratChecker f8584 p8584 = .success := by decide +kernel
theorem unsat8584 : Unsatisfiable (PosFin 65) f8584 := by
  apply lratCheckerSound f8584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8584
  · intro a ha; simp [p8584] at ha; subst a; trivial
  · exact checked8584
theorem derived8584 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8584 := by
  apply localUnsat_implies_entails f8584 [c8579, c8580, c8562, c8523, c8380, c8421, c8486, c8582, c8583, c692, c685, c697, c8510, c8511, c8532, c237, c235] c8584 unsat8584 (by rfl) a
  have h0 : Entails.eval a c8579 := derived8579 a h
  have h1 : Entails.eval a c8580 := derived8580 a h
  have h2 : Entails.eval a c8562 := derived8562 a h
  have h3 : Entails.eval a c8523 := derived8523 a h
  have h4 : Entails.eval a c8380 := derived8380 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8486 := derived8486 a h
  have h7 : Entails.eval a c8582 := derived8582 a h
  have h8 : Entails.eval a c8583 := derived8583 a h
  have h9 : Entails.eval a c692 := h 691 (by decide)
  have h10 : Entails.eval a c685 := h 684 (by decide)
  have h11 : Entails.eval a c697 := h 696 (by decide)
  have h12 : Entails.eval a c8510 := derived8510 a h
  have h13 : Entails.eval a c8511 := derived8511 a h
  have h14 : Entails.eval a c8532 := derived8532 a h
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8585 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8585 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8580, some c8505, some c8380, some c675, some c667, some c8582, some c682, some c685, some c8391, some c1223, some c1231, some c1178, some c1200, some c1184, some c1206, some c1218, some c1436, some c1173, some c1399, some c5381, some c192, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8585 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8585 : lratChecker f8585 p8585 = .success := by decide +kernel
theorem unsat8585 : Unsatisfiable (PosFin 65) f8585 := by
  apply lratCheckerSound f8585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8585
  · intro a ha; simp [p8585] at ha; subst a; trivial
  · exact checked8585
theorem derived8585 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8585 := by
  apply localUnsat_implies_entails f8585 [c8580, c8505, c8380, c675, c667, c8582, c682, c685, c8391, c1223, c1231, c1178, c1200, c1184, c1206, c1218, c1436, c1173, c1399, c5381, c192] c8585 unsat8585 (by rfl) a
  have h0 : Entails.eval a c8580 := derived8580 a h
  have h1 : Entails.eval a c8505 := derived8505 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c675 := h 674 (by decide)
  have h4 : Entails.eval a c667 := h 666 (by decide)
  have h5 : Entails.eval a c8582 := derived8582 a h
  have h6 : Entails.eval a c682 := h 681 (by decide)
  have h7 : Entails.eval a c685 := h 684 (by decide)
  have h8 : Entails.eval a c8391 := derived8391 a h
  have h9 : Entails.eval a c1223 := h 1222 (by decide)
  have h10 : Entails.eval a c1231 := h 1230 (by decide)
  have h11 : Entails.eval a c1178 := h 1177 (by decide)
  have h12 : Entails.eval a c1200 := h 1199 (by decide)
  have h13 : Entails.eval a c1184 := h 1183 (by decide)
  have h14 : Entails.eval a c1206 := h 1205 (by decide)
  have h15 : Entails.eval a c1218 := h 1217 (by decide)
  have h16 : Entails.eval a c1436 := h 1435 (by decide)
  have h17 : Entails.eval a c1173 := h 1172 (by decide)
  have h18 : Entails.eval a c1399 := h 1398 (by decide)
  have h19 : Entails.eval a c5381 := h 5380 (by decide)
  have h20 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8586 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨53, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8586 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c408, some c448, some c167, some c287, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8586 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8586 : lratChecker f8586 p8586 = .success := by decide +kernel
theorem unsat8586 : Unsatisfiable (PosFin 65) f8586 := by
  apply lratCheckerSound f8586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8586
  · intro a ha; simp [p8586] at ha; subst a; trivial
  · exact checked8586
theorem derived8586 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8586 := by
  apply localUnsat_implies_entails f8586 [c408, c448, c167, c287] c8586 unsat8586 (by rfl) a
  have h0 : Entails.eval a c408 := h 407 (by decide)
  have h1 : Entails.eval a c448 := h 447 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8587 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨34, by decide⟩, true), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8587 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c265, some c5286, some c5270, some c941, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8587 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8587 : lratChecker f8587 p8587 = .success := by decide +kernel
theorem unsat8587 : Unsatisfiable (PosFin 65) f8587 := by
  apply lratCheckerSound f8587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8587
  · intro a ha; simp [p8587] at ha; subst a; trivial
  · exact checked8587
theorem derived8587 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8587 := by
  apply localUnsat_implies_entails f8587 [c265, c5286, c5270, c941] c8587 unsat8587 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c5286 := h 5285 (by decide)
  have h2 : Entails.eval a c5270 := h 5269 (by decide)
  have h3 : Entails.eval a c941 := h 940 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8588 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8588 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8579, some c8562, some c8523, some c8380, some c8421, some c8505, some c8580, some c8584, some c8585, some c8583, some c692, some c685, some c697, some c668, some c8510, some c1178, some c1124, some c4428, some c8532, some c2767, some c4702, some c226, some c225, some c8511, some c997, some c219, some c4200, some c300, some c328, some c8586, some c8587, some c501, some c971, some c263, some c95, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8588 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked8588 : lratChecker f8588 p8588 = .success := by decide +kernel
theorem unsat8588 : Unsatisfiable (PosFin 65) f8588 := by
  apply lratCheckerSound f8588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8588
  · intro a ha; simp [p8588] at ha; subst a; trivial
  · exact checked8588
theorem derived8588 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8588 := by
  apply localUnsat_implies_entails f8588 [c8579, c8562, c8523, c8380, c8421, c8505, c8580, c8584, c8585, c8583, c692, c685, c697, c668, c8510, c1178, c1124, c4428, c8532, c2767, c4702, c226, c225, c8511, c997, c219, c4200, c300, c328, c8586, c8587, c501, c971, c263, c95] c8588 unsat8588 (by rfl) a
  have h0 : Entails.eval a c8579 := derived8579 a h
  have h1 : Entails.eval a c8562 := derived8562 a h
  have h2 : Entails.eval a c8523 := derived8523 a h
  have h3 : Entails.eval a c8380 := derived8380 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c8505 := derived8505 a h
  have h6 : Entails.eval a c8580 := derived8580 a h
  have h7 : Entails.eval a c8584 := derived8584 a h
  have h8 : Entails.eval a c8585 := derived8585 a h
  have h9 : Entails.eval a c8583 := derived8583 a h
  have h10 : Entails.eval a c692 := h 691 (by decide)
  have h11 : Entails.eval a c685 := h 684 (by decide)
  have h12 : Entails.eval a c697 := h 696 (by decide)
  have h13 : Entails.eval a c668 := h 667 (by decide)
  have h14 : Entails.eval a c8510 := derived8510 a h
  have h15 : Entails.eval a c1178 := h 1177 (by decide)
  have h16 : Entails.eval a c1124 := h 1123 (by decide)
  have h17 : Entails.eval a c4428 := h 4427 (by decide)
  have h18 : Entails.eval a c8532 := derived8532 a h
  have h19 : Entails.eval a c2767 := h 2766 (by decide)
  have h20 : Entails.eval a c4702 := h 4701 (by decide)
  have h21 : Entails.eval a c226 := h 225 (by decide)
  have h22 : Entails.eval a c225 := h 224 (by decide)
  have h23 : Entails.eval a c8511 := derived8511 a h
  have h24 : Entails.eval a c997 := h 996 (by decide)
  have h25 : Entails.eval a c219 := h 218 (by decide)
  have h26 : Entails.eval a c4200 := h 4199 (by decide)
  have h27 : Entails.eval a c300 := h 299 (by decide)
  have h28 : Entails.eval a c328 := h 327 (by decide)
  have h29 : Entails.eval a c8586 := derived8586 a h
  have h30 : Entails.eval a c8587 := derived8587 a h
  have h31 : Entails.eval a c501 := h 500 (by decide)
  have h32 : Entails.eval a c971 := h 970 (by decide)
  have h33 : Entails.eval a c263 := h 262 (by decide)
  have h34 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8589 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8589 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c46, some c15, some c28, some c6558, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8589 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8589 : lratChecker f8589 p8589 = .success := by decide +kernel
theorem unsat8589 : Unsatisfiable (PosFin 65) f8589 := by
  apply lratCheckerSound f8589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8589
  · intro a ha; simp [p8589] at ha; subst a; trivial
  · exact checked8589
theorem derived8589 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8589 := by
  apply localUnsat_implies_entails f8589 [c46, c15, c28, c6558] c8589 unsat8589 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c6558 := h 6557 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8590 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨20, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8590 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6000, some c6001, some c5992, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p8590 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8590 : lratChecker f8590 p8590 = .success := by decide +kernel
theorem unsat8590 : Unsatisfiable (PosFin 65) f8590 := by
  apply lratCheckerSound f8590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8590
  · intro a ha; simp [p8590] at ha; subst a; trivial
  · exact checked8590
theorem derived8590 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8590 := by
  apply localUnsat_implies_entails f8590 [c6000, c6001, c5992] c8590 unsat8590 (by rfl) a
  have h0 : Entails.eval a c6000 := h 5999 (by decide)
  have h1 : Entails.eval a c6001 := h 6000 (by decide)
  have h2 : Entails.eval a c5992 := h 5991 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8591 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8591 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8562, some c8579, some c8588, some c8589, some c8523, some c8530, some c8541, some c6140, some c8542, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8591 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8591 : lratChecker f8591 p8591 = .success := by decide +kernel
theorem unsat8591 : Unsatisfiable (PosFin 65) f8591 := by
  apply lratCheckerSound f8591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8591
  · intro a ha; simp [p8591] at ha; subst a; trivial
  · exact checked8591
theorem derived8591 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8591 := by
  apply localUnsat_implies_entails f8591 [c8380, c8562, c8579, c8588, c8589, c8523, c8530, c8541, c6140, c8542] c8591 unsat8591 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8562 := derived8562 a h
  have h2 : Entails.eval a c8579 := derived8579 a h
  have h3 : Entails.eval a c8588 := derived8588 a h
  have h4 : Entails.eval a c8589 := derived8589 a h
  have h5 : Entails.eval a c8523 := derived8523 a h
  have h6 : Entails.eval a c8530 := derived8530 a h
  have h7 : Entails.eval a c8541 := derived8541 a h
  have h8 : Entails.eval a c6140 := h 6139 (by decide)
  have h9 : Entails.eval a c8542 := derived8542 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8592 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨20, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8592 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8532, some c5885, some c5886, some c790, some c5882, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8592 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8592 : lratChecker f8592 p8592 = .success := by decide +kernel
theorem unsat8592 : Unsatisfiable (PosFin 65) f8592 := by
  apply lratCheckerSound f8592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8592
  · intro a ha; simp [p8592] at ha; subst a; trivial
  · exact checked8592
theorem derived8592 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8592 := by
  apply localUnsat_implies_entails f8592 [c8532, c5885, c5886, c790, c5882] c8592 unsat8592 (by rfl) a
  have h0 : Entails.eval a c8532 := derived8532 a h
  have h1 : Entails.eval a c5885 := h 5884 (by decide)
  have h2 : Entails.eval a c5886 := h 5885 (by decide)
  have h3 : Entails.eval a c790 := h 789 (by decide)
  have h4 : Entails.eval a c5882 := h 5881 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8593 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8593 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6140, some c8542, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8593 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8593 : lratChecker f8593 p8593 = .success := by decide +kernel
theorem unsat8593 : Unsatisfiable (PosFin 65) f8593 := by
  apply lratCheckerSound f8593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8593
  · intro a ha; simp [p8593] at ha; subst a; trivial
  · exact checked8593
theorem derived8593 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8593 := by
  apply localUnsat_implies_entails f8593 [c6140, c8542] c8593 unsat8593 (by rfl) a
  have h0 : Entails.eval a c6140 := h 6139 (by decide)
  have h1 : Entails.eval a c8542 := derived8542 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8594 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8594 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8562, some c8579, some c8588, some c8589, some c8523, some c8421, some c8590, some c8592, some c8591, some c8593, some c1257, some c886, some c1186, some c4702, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8594 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8594 : lratChecker f8594 p8594 = .success := by decide +kernel
theorem unsat8594 : Unsatisfiable (PosFin 65) f8594 := by
  apply lratCheckerSound f8594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8594
  · intro a ha; simp [p8594] at ha; subst a; trivial
  · exact checked8594
theorem derived8594 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8594 := by
  apply localUnsat_implies_entails f8594 [c8380, c8562, c8579, c8588, c8589, c8523, c8421, c8590, c8592, c8591, c8593, c1257, c886, c1186, c4702] c8594 unsat8594 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8562 := derived8562 a h
  have h2 : Entails.eval a c8579 := derived8579 a h
  have h3 : Entails.eval a c8588 := derived8588 a h
  have h4 : Entails.eval a c8589 := derived8589 a h
  have h5 : Entails.eval a c8523 := derived8523 a h
  have h6 : Entails.eval a c8421 := derived8421 a h
  have h7 : Entails.eval a c8590 := derived8590 a h
  have h8 : Entails.eval a c8592 := derived8592 a h
  have h9 : Entails.eval a c8591 := derived8591 a h
  have h10 : Entails.eval a c8593 := derived8593 a h
  have h11 : Entails.eval a c1257 := h 1256 (by decide)
  have h12 : Entails.eval a c886 := h 885 (by decide)
  have h13 : Entails.eval a c1186 := h 1185 (by decide)
  have h14 : Entails.eval a c4702 := h 4701 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8595 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8595 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c904, some c906, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8595 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8595 : lratChecker f8595 p8595 = .success := by decide +kernel
theorem unsat8595 : Unsatisfiable (PosFin 65) f8595 := by
  apply lratCheckerSound f8595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8595
  · intro a ha; simp [p8595] at ha; subst a; trivial
  · exact checked8595
theorem derived8595 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8595 := by
  apply localUnsat_implies_entails f8595 [c904, c906] c8595 unsat8595 (by rfl) a
  have h0 : Entails.eval a c904 := h 903 (by decide)
  have h1 : Entails.eval a c906 := h 905 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8596 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨20, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8596 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1223, some c1231, some c311, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8596 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8596 : lratChecker f8596 p8596 = .success := by decide +kernel
theorem unsat8596 : Unsatisfiable (PosFin 65) f8596 := by
  apply lratCheckerSound f8596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8596
  · intro a ha; simp [p8596] at ha; subst a; trivial
  · exact checked8596
theorem derived8596 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8596 := by
  apply localUnsat_implies_entails f8596 [c1223, c1231, c311] c8596 unsat8596 (by rfl) a
  have h0 : Entails.eval a c1223 := h 1222 (by decide)
  have h1 : Entails.eval a c1231 := h 1230 (by decide)
  have h2 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8597 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8597 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8572, some c8595, some c8596, some c4899, some c4920, some c4897, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8597 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8597 : lratChecker f8597 p8597 = .success := by decide +kernel
theorem unsat8597 : Unsatisfiable (PosFin 65) f8597 := by
  apply lratCheckerSound f8597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8597
  · intro a ha; simp [p8597] at ha; subst a; trivial
  · exact checked8597
theorem derived8597 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8597 := by
  apply localUnsat_implies_entails f8597 [c8572, c8595, c8596, c4899, c4920, c4897] c8597 unsat8597 (by rfl) a
  have h0 : Entails.eval a c8572 := derived8572 a h
  have h1 : Entails.eval a c8595 := derived8595 a h
  have h2 : Entails.eval a c8596 := derived8596 a h
  have h3 : Entails.eval a c4899 := h 4898 (by decide)
  have h4 : Entails.eval a c4920 := h 4919 (by decide)
  have h5 : Entails.eval a c4897 := h 4896 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8598 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8598 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8380, some c8523, some c8562, some c8588, some c8579, some c8589, some c8594, some c8597, some c8593, some c8541, some c6170, some c6165, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8598 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8598 : lratChecker f8598 p8598 = .success := by decide +kernel
theorem unsat8598 : Unsatisfiable (PosFin 65) f8598 := by
  apply lratCheckerSound f8598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8598
  · intro a ha; simp [p8598] at ha; subst a; trivial
  · exact checked8598
theorem derived8598 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8598 := by
  apply localUnsat_implies_entails f8598 [c8421, c8380, c8523, c8562, c8588, c8579, c8589, c8594, c8597, c8593, c8541, c6170, c6165] c8598 unsat8598 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c8523 := derived8523 a h
  have h3 : Entails.eval a c8562 := derived8562 a h
  have h4 : Entails.eval a c8588 := derived8588 a h
  have h5 : Entails.eval a c8579 := derived8579 a h
  have h6 : Entails.eval a c8589 := derived8589 a h
  have h7 : Entails.eval a c8594 := derived8594 a h
  have h8 : Entails.eval a c8597 := derived8597 a h
  have h9 : Entails.eval a c8593 := derived8593 a h
  have h10 : Entails.eval a c8541 := derived8541 a h
  have h11 : Entails.eval a c6170 := h 6169 (by decide)
  have h12 : Entails.eval a c6165 := h 6164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8599 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8599 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8579, some c8562, some c8523, some c8380, some c8421, some c8588, some c8589, some c8594, some c8597, some c8598, some c1178, some c1124, some c4428, some c8532, some c922, some c933, some c215, some c218, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8599 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8599 : lratChecker f8599 p8599 = .success := by decide +kernel
theorem unsat8599 : Unsatisfiable (PosFin 65) f8599 := by
  apply lratCheckerSound f8599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8599
  · intro a ha; simp [p8599] at ha; subst a; trivial
  · exact checked8599
theorem derived8599 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8599 := by
  apply localUnsat_implies_entails f8599 [c8579, c8562, c8523, c8380, c8421, c8588, c8589, c8594, c8597, c8598, c1178, c1124, c4428, c8532, c922, c933, c215, c218] c8599 unsat8599 (by rfl) a
  have h0 : Entails.eval a c8579 := derived8579 a h
  have h1 : Entails.eval a c8562 := derived8562 a h
  have h2 : Entails.eval a c8523 := derived8523 a h
  have h3 : Entails.eval a c8380 := derived8380 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c8588 := derived8588 a h
  have h6 : Entails.eval a c8589 := derived8589 a h
  have h7 : Entails.eval a c8594 := derived8594 a h
  have h8 : Entails.eval a c8597 := derived8597 a h
  have h9 : Entails.eval a c8598 := derived8598 a h
  have h10 : Entails.eval a c1178 := h 1177 (by decide)
  have h11 : Entails.eval a c1124 := h 1123 (by decide)
  have h12 : Entails.eval a c4428 := h 4427 (by decide)
  have h13 : Entails.eval a c8532 := derived8532 a h
  have h14 : Entails.eval a c922 := h 921 (by decide)
  have h15 : Entails.eval a c933 := h 932 (by decide)
  have h16 : Entails.eval a c215 := h 214 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8600 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨49, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8600 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c675, some c667, some c1189, some c4882, some c8595, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8600 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8600 : lratChecker f8600 p8600 = .success := by decide +kernel
theorem unsat8600 : Unsatisfiable (PosFin 65) f8600 := by
  apply lratCheckerSound f8600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8600
  · intro a ha; simp [p8600] at ha; subst a; trivial
  · exact checked8600
theorem derived8600 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8600 := by
  apply localUnsat_implies_entails f8600 [c675, c667, c1189, c4882, c8595] c8600 unsat8600 (by rfl) a
  have h0 : Entails.eval a c675 := h 674 (by decide)
  have h1 : Entails.eval a c667 := h 666 (by decide)
  have h2 : Entails.eval a c1189 := h 1188 (by decide)
  have h3 : Entails.eval a c4882 := h 4881 (by decide)
  have h4 : Entails.eval a c8595 := derived8595 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8601 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8601 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8599, some c8579, some c8562, some c8523, some c8421, some c8580, some c8600, some c8583, some c692, some c685, some c658, some c657, some c668, some c8510, some c577, some c626, some c5926, some c1193, some c4885, some c225, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8601 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8601 : lratChecker f8601 p8601 = .success := by decide +kernel
theorem unsat8601 : Unsatisfiable (PosFin 65) f8601 := by
  apply lratCheckerSound f8601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8601
  · intro a ha; simp [p8601] at ha; subst a; trivial
  · exact checked8601
theorem derived8601 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8601 := by
  apply localUnsat_implies_entails f8601 [c8599, c8579, c8562, c8523, c8421, c8580, c8600, c8583, c692, c685, c658, c657, c668, c8510, c577, c626, c5926, c1193, c4885, c225] c8601 unsat8601 (by rfl) a
  have h0 : Entails.eval a c8599 := derived8599 a h
  have h1 : Entails.eval a c8579 := derived8579 a h
  have h2 : Entails.eval a c8562 := derived8562 a h
  have h3 : Entails.eval a c8523 := derived8523 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c8580 := derived8580 a h
  have h6 : Entails.eval a c8600 := derived8600 a h
  have h7 : Entails.eval a c8583 := derived8583 a h
  have h8 : Entails.eval a c692 := h 691 (by decide)
  have h9 : Entails.eval a c685 := h 684 (by decide)
  have h10 : Entails.eval a c658 := h 657 (by decide)
  have h11 : Entails.eval a c657 := h 656 (by decide)
  have h12 : Entails.eval a c668 := h 667 (by decide)
  have h13 : Entails.eval a c8510 := derived8510 a h
  have h14 : Entails.eval a c577 := h 576 (by decide)
  have h15 : Entails.eval a c626 := h 625 (by decide)
  have h16 : Entails.eval a c5926 := h 5925 (by decide)
  have h17 : Entails.eval a c1193 := h 1192 (by decide)
  have h18 : Entails.eval a c4885 := h 4884 (by decide)
  have h19 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8602 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨49, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8602 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8572, some c8486, some c4896, some c5797, some c904, some c905, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8602 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8602 : lratChecker f8602 p8602 = .success := by decide +kernel
theorem unsat8602 : Unsatisfiable (PosFin 65) f8602 := by
  apply lratCheckerSound f8602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8602
  · intro a ha; simp [p8602] at ha; subst a; trivial
  · exact checked8602
theorem derived8602 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8602 := by
  apply localUnsat_implies_entails f8602 [c8380, c8572, c8486, c4896, c5797, c904, c905] c8602 unsat8602 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8572 := derived8572 a h
  have h2 : Entails.eval a c8486 := derived8486 a h
  have h3 : Entails.eval a c4896 := h 4895 (by decide)
  have h4 : Entails.eval a c5797 := h 5796 (by decide)
  have h5 : Entails.eval a c904 := h 903 (by decide)
  have h6 : Entails.eval a c905 := h 904 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8603 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨49, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8603 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1223, some c1231, some c281, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8603 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8603 : lratChecker f8603 p8603 = .success := by decide +kernel
theorem unsat8603 : Unsatisfiable (PosFin 65) f8603 := by
  apply lratCheckerSound f8603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8603
  · intro a ha; simp [p8603] at ha; subst a; trivial
  · exact checked8603
theorem derived8603 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8603 := by
  apply localUnsat_implies_entails f8603 [c1223, c1231, c281] c8603 unsat8603 (by rfl) a
  have h0 : Entails.eval a c1223 := h 1222 (by decide)
  have h1 : Entails.eval a c1231 := h 1230 (by decide)
  have h2 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8604 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8604 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4899, some c4897, some c4920, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8604 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8604 : lratChecker f8604 p8604 = .success := by decide +kernel
theorem unsat8604 : Unsatisfiable (PosFin 65) f8604 := by
  apply lratCheckerSound f8604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8604
  · intro a ha; simp [p8604] at ha; subst a; trivial
  · exact checked8604
theorem derived8604 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8604 := by
  apply localUnsat_implies_entails f8604 [c4899, c4897, c4920] c8604 unsat8604 (by rfl) a
  have h0 : Entails.eval a c4899 := h 4898 (by decide)
  have h1 : Entails.eval a c4897 := h 4896 (by decide)
  have h2 : Entails.eval a c4920 := h 4919 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8605 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨49, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8605 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8572, some c8602, some c8603, some c8604, some c904, some c905, some c926, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8605 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8605 : lratChecker f8605 p8605 = .success := by decide +kernel
theorem unsat8605 : Unsatisfiable (PosFin 65) f8605 := by
  apply lratCheckerSound f8605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8605
  · intro a ha; simp [p8605] at ha; subst a; trivial
  · exact checked8605
theorem derived8605 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8605 := by
  apply localUnsat_implies_entails f8605 [c8380, c8572, c8602, c8603, c8604, c904, c905, c926] c8605 unsat8605 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8572 := derived8572 a h
  have h2 : Entails.eval a c8602 := derived8602 a h
  have h3 : Entails.eval a c8603 := derived8603 a h
  have h4 : Entails.eval a c8604 := derived8604 a h
  have h5 : Entails.eval a c904 := h 903 (by decide)
  have h6 : Entails.eval a c905 := h 904 (by decide)
  have h7 : Entails.eval a c926 := h 925 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8606 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8606 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8486, some c4896, some c2734, some c228, some c4450, some c6089, some c213, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8606 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8606 : lratChecker f8606 p8606 = .success := by decide +kernel
theorem unsat8606 : Unsatisfiable (PosFin 65) f8606 := by
  apply lratCheckerSound f8606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8606
  · intro a ha; simp [p8606] at ha; subst a; trivial
  · exact checked8606
theorem derived8606 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8606 := by
  apply localUnsat_implies_entails f8606 [c8380, c8486, c4896, c2734, c228, c4450, c6089, c213] c8606 unsat8606 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8486 := derived8486 a h
  have h2 : Entails.eval a c4896 := h 4895 (by decide)
  have h3 : Entails.eval a c2734 := h 2733 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c4450 := h 4449 (by decide)
  have h6 : Entails.eval a c6089 := h 6088 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8607 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8607 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1223, some c1231, some c3823, some c4219, some c3042, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8607 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8607 : lratChecker f8607 p8607 = .success := by decide +kernel
theorem unsat8607 : Unsatisfiable (PosFin 65) f8607 := by
  apply lratCheckerSound f8607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8607
  · intro a ha; simp [p8607] at ha; subst a; trivial
  · exact checked8607
theorem derived8607 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8607 := by
  apply localUnsat_implies_entails f8607 [c1223, c1231, c3823, c4219, c3042] c8607 unsat8607 (by rfl) a
  have h0 : Entails.eval a c1223 := h 1222 (by decide)
  have h1 : Entails.eval a c1231 := h 1230 (by decide)
  have h2 : Entails.eval a c3823 := h 3822 (by decide)
  have h3 : Entails.eval a c4219 := h 4218 (by decide)
  have h4 : Entails.eval a c3042 := h 3041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8608 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8608 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c916, some c919, some c791, some c5936, some c5937, some c5929, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8608 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8608 : lratChecker f8608 p8608 = .success := by decide +kernel
theorem unsat8608 : Unsatisfiable (PosFin 65) f8608 := by
  apply lratCheckerSound f8608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8608
  · intro a ha; simp [p8608] at ha; subst a; trivial
  · exact checked8608
theorem derived8608 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8608 := by
  apply localUnsat_implies_entails f8608 [c916, c919, c791, c5936, c5937, c5929] c8608 unsat8608 (by rfl) a
  have h0 : Entails.eval a c916 := h 915 (by decide)
  have h1 : Entails.eval a c919 := h 918 (by decide)
  have h2 : Entails.eval a c791 := h 790 (by decide)
  have h3 : Entails.eval a c5936 := h 5935 (by decide)
  have h4 : Entails.eval a c5937 := h 5936 (by decide)
  have h5 : Entails.eval a c5929 := h 5928 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8609 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8609 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c931, some c906, some c903, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8609 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8609 : lratChecker f8609 p8609 = .success := by decide +kernel
theorem unsat8609 : Unsatisfiable (PosFin 65) f8609 := by
  apply lratCheckerSound f8609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8609
  · intro a ha; simp [p8609] at ha; subst a; trivial
  · exact checked8609
theorem derived8609 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8609 := by
  apply localUnsat_implies_entails f8609 [c931, c906, c903] c8609 unsat8609 (by rfl) a
  have h0 : Entails.eval a c931 := h 930 (by decide)
  have h1 : Entails.eval a c906 := h 905 (by decide)
  have h2 : Entails.eval a c903 := h 902 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8610 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8610 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8380, some c8523, some c8562, some c8579, some c8599, some c8601, some c8605, some c8606, some c8607, some c8604, some c8608, some c8609, some c920, some c933, some c913, some c6015, some c6022, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8610 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8610 : lratChecker f8610 p8610 = .success := by decide +kernel
theorem unsat8610 : Unsatisfiable (PosFin 65) f8610 := by
  apply lratCheckerSound f8610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8610
  · intro a ha; simp [p8610] at ha; subst a; trivial
  · exact checked8610
theorem derived8610 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8610 := by
  apply localUnsat_implies_entails f8610 [c8421, c8380, c8523, c8562, c8579, c8599, c8601, c8605, c8606, c8607, c8604, c8608, c8609, c920, c933, c913, c6015, c6022] c8610 unsat8610 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c8523 := derived8523 a h
  have h3 : Entails.eval a c8562 := derived8562 a h
  have h4 : Entails.eval a c8579 := derived8579 a h
  have h5 : Entails.eval a c8599 := derived8599 a h
  have h6 : Entails.eval a c8601 := derived8601 a h
  have h7 : Entails.eval a c8605 := derived8605 a h
  have h8 : Entails.eval a c8606 := derived8606 a h
  have h9 : Entails.eval a c8607 := derived8607 a h
  have h10 : Entails.eval a c8604 := derived8604 a h
  have h11 : Entails.eval a c8608 := derived8608 a h
  have h12 : Entails.eval a c8609 := derived8609 a h
  have h13 : Entails.eval a c920 := h 919 (by decide)
  have h14 : Entails.eval a c933 := h 932 (by decide)
  have h15 : Entails.eval a c913 := h 912 (by decide)
  have h16 : Entails.eval a c6015 := h 6014 (by decide)
  have h17 : Entails.eval a c6022 := h 6021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8611 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨24, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8611 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5891, some c576, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8611 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8611 : lratChecker f8611 p8611 = .success := by decide +kernel
theorem unsat8611 : Unsatisfiable (PosFin 65) f8611 := by
  apply lratCheckerSound f8611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8611
  · intro a ha; simp [p8611] at ha; subst a; trivial
  · exact checked8611
theorem derived8611 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8611 := by
  apply localUnsat_implies_entails f8611 [c5891, c576] c8611 unsat8611 (by rfl) a
  have h0 : Entails.eval a c5891 := h 5890 (by decide)
  have h1 : Entails.eval a c576 := h 575 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8612 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8612 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8426, some c8490, some c8496, some c702, some c706, some c654, some c8436, some c681, some c8611, some c6017, some c5584, some c5703, some c5598, some c5705, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8612 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8612 : lratChecker f8612 p8612 = .success := by decide +kernel
theorem unsat8612 : Unsatisfiable (PosFin 65) f8612 := by
  apply lratCheckerSound f8612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8612
  · intro a ha; simp [p8612] at ha; subst a; trivial
  · exact checked8612
theorem derived8612 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8612 := by
  apply localUnsat_implies_entails f8612 [c8426, c8490, c8496, c702, c706, c654, c8436, c681, c8611, c6017, c5584, c5703, c5598, c5705] c8612 unsat8612 (by rfl) a
  have h0 : Entails.eval a c8426 := derived8426 a h
  have h1 : Entails.eval a c8490 := derived8490 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c702 := h 701 (by decide)
  have h4 : Entails.eval a c706 := h 705 (by decide)
  have h5 : Entails.eval a c654 := h 653 (by decide)
  have h6 : Entails.eval a c8436 := derived8436 a h
  have h7 : Entails.eval a c681 := h 680 (by decide)
  have h8 : Entails.eval a c8611 := derived8611 a h
  have h9 : Entails.eval a c6017 := h 6016 (by decide)
  have h10 : Entails.eval a c5584 := h 5583 (by decide)
  have h11 : Entails.eval a c5703 := h 5702 (by decide)
  have h12 : Entails.eval a c5598 := h 5597 (by decide)
  have h13 : Entails.eval a c5705 := h 5704 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8613 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8613 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c667, some c675, some c8438, some c655, some c8435, some c671, some c685, some c703, some c698, some c8611, some c6017, some c581, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8613 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8613 : lratChecker f8613 p8613 = .success := by decide +kernel
theorem unsat8613 : Unsatisfiable (PosFin 65) f8613 := by
  apply lratCheckerSound f8613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8613
  · intro a ha; simp [p8613] at ha; subst a; trivial
  · exact checked8613
theorem derived8613 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8613 := by
  apply localUnsat_implies_entails f8613 [c667, c675, c8438, c655, c8435, c671, c685, c703, c698, c8611, c6017, c581] c8613 unsat8613 (by rfl) a
  have h0 : Entails.eval a c667 := h 666 (by decide)
  have h1 : Entails.eval a c675 := h 674 (by decide)
  have h2 : Entails.eval a c8438 := derived8438 a h
  have h3 : Entails.eval a c655 := h 654 (by decide)
  have h4 : Entails.eval a c8435 := derived8435 a h
  have h5 : Entails.eval a c671 := h 670 (by decide)
  have h6 : Entails.eval a c685 := h 684 (by decide)
  have h7 : Entails.eval a c703 := h 702 (by decide)
  have h8 : Entails.eval a c698 := h 697 (by decide)
  have h9 : Entails.eval a c8611 := derived8611 a h
  have h10 : Entails.eval a c6017 := h 6016 (by decide)
  have h11 : Entails.eval a c581 := h 580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8614 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8614 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5383, some c169, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8614 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8614 : lratChecker f8614 p8614 = .success := by decide +kernel
theorem unsat8614 : Unsatisfiable (PosFin 65) f8614 := by
  apply lratCheckerSound f8614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8614
  · intro a ha; simp [p8614] at ha; subst a; trivial
  · exact checked8614
theorem derived8614 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8614 := by
  apply localUnsat_implies_entails f8614 [c5383, c169] c8614 unsat8614 (by rfl) a
  have h0 : Entails.eval a c5383 := h 5382 (by decide)
  have h1 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8615 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨50, by decide⟩, false), (⟨22, by decide⟩, true), (⟨36, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8615 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5358, some c5353, some c5362, some c376, some c5473, some c379, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8615 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8615 : lratChecker f8615 p8615 = .success := by decide +kernel
theorem unsat8615 : Unsatisfiable (PosFin 65) f8615 := by
  apply lratCheckerSound f8615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8615
  · intro a ha; simp [p8615] at ha; subst a; trivial
  · exact checked8615
theorem derived8615 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8615 := by
  apply localUnsat_implies_entails f8615 [c5358, c5353, c5362, c376, c5473, c379] c8615 unsat8615 (by rfl) a
  have h0 : Entails.eval a c5358 := h 5357 (by decide)
  have h1 : Entails.eval a c5353 := h 5352 (by decide)
  have h2 : Entails.eval a c5362 := h 5361 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c5473 := h 5472 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8616 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨34, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨36, by decide⟩, true), (⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8616 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5264, some c5265, some c5266, some c5295, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p8616 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8616 : lratChecker f8616 p8616 = .success := by decide +kernel
theorem unsat8616 : Unsatisfiable (PosFin 65) f8616 := by
  apply lratCheckerSound f8616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8616
  · intro a ha; simp [p8616] at ha; subst a; trivial
  · exact checked8616
theorem derived8616 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8616 := by
  apply localUnsat_implies_entails f8616 [c5264, c5265, c5266, c5295] c8616 unsat8616 (by rfl) a
  have h0 : Entails.eval a c5264 := h 5263 (by decide)
  have h1 : Entails.eval a c5265 := h 5264 (by decide)
  have h2 : Entails.eval a c5266 := h 5265 (by decide)
  have h3 : Entails.eval a c5295 := h 5294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8617 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨36, by decide⟩, true), (⟨28, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8617 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8614, some c8615, some c375, some c141, some c142, some c8616, some c190, some c138, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8617 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8617 : lratChecker f8617 p8617 = .success := by decide +kernel
theorem unsat8617 : Unsatisfiable (PosFin 65) f8617 := by
  apply lratCheckerSound f8617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8617
  · intro a ha; simp [p8617] at ha; subst a; trivial
  · exact checked8617
theorem derived8617 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8617 := by
  apply localUnsat_implies_entails f8617 [c8614, c8615, c375, c141, c142, c8616, c190, c138] c8617 unsat8617 (by rfl) a
  have h0 : Entails.eval a c8614 := derived8614 a h
  have h1 : Entails.eval a c8615 := derived8615 a h
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c8616 := derived8616 a h
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8618 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, true), (⟨36, by decide⟩, true), (⟨28, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8618 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8617, some c6017, some c581, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8618 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8618 : lratChecker f8618 p8618 = .success := by decide +kernel
theorem unsat8618 : Unsatisfiable (PosFin 65) f8618 := by
  apply lratCheckerSound f8618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8618
  · intro a ha; simp [p8618] at ha; subst a; trivial
  · exact checked8618
theorem derived8618 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8618 := by
  apply localUnsat_implies_entails f8618 [c8617, c6017, c581] c8618 unsat8618 (by rfl) a
  have h0 : Entails.eval a c8617 := derived8617 a h
  have h1 : Entails.eval a c6017 := h 6016 (by decide)
  have h2 : Entails.eval a c581 := h 580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8619 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8619 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8610, some c8612, some c675, some c667, some c682, some c8613, some c8505, some c8580, some c685, some c8391, some c676, some c661, some c698, some c688, some c8618, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8619 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8619 : lratChecker f8619 p8619 = .success := by decide +kernel
theorem unsat8619 : Unsatisfiable (PosFin 65) f8619 := by
  apply lratCheckerSound f8619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8619
  · intro a ha; simp [p8619] at ha; subst a; trivial
  · exact checked8619
theorem derived8619 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8619 := by
  apply localUnsat_implies_entails f8619 [c8610, c8612, c675, c667, c682, c8613, c8505, c8580, c685, c8391, c676, c661, c698, c688, c8618] c8619 unsat8619 (by rfl) a
  have h0 : Entails.eval a c8610 := derived8610 a h
  have h1 : Entails.eval a c8612 := derived8612 a h
  have h2 : Entails.eval a c675 := h 674 (by decide)
  have h3 : Entails.eval a c667 := h 666 (by decide)
  have h4 : Entails.eval a c682 := h 681 (by decide)
  have h5 : Entails.eval a c8613 := derived8613 a h
  have h6 : Entails.eval a c8505 := derived8505 a h
  have h7 : Entails.eval a c8580 := derived8580 a h
  have h8 : Entails.eval a c685 := h 684 (by decide)
  have h9 : Entails.eval a c8391 := derived8391 a h
  have h10 : Entails.eval a c676 := h 675 (by decide)
  have h11 : Entails.eval a c661 := h 660 (by decide)
  have h12 : Entails.eval a c698 := h 697 (by decide)
  have h13 : Entails.eval a c688 := h 687 (by decide)
  have h14 : Entails.eval a c8618 := derived8618 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8620 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8620 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8426, some c8490, some c654, some c6004, some c8498, some c5897, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8620 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8620 : lratChecker f8620 p8620 = .success := by decide +kernel
theorem unsat8620 : Unsatisfiable (PosFin 65) f8620 := by
  apply lratCheckerSound f8620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8620
  · intro a ha; simp [p8620] at ha; subst a; trivial
  · exact checked8620
theorem derived8620 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8620 := by
  apply localUnsat_implies_entails f8620 [c8426, c8490, c654, c6004, c8498, c5897] c8620 unsat8620 (by rfl) a
  have h0 : Entails.eval a c8426 := derived8426 a h
  have h1 : Entails.eval a c8490 := derived8490 a h
  have h2 : Entails.eval a c654 := h 653 (by decide)
  have h3 : Entails.eval a c6004 := h 6003 (by decide)
  have h4 : Entails.eval a c8498 := derived8498 a h
  have h5 : Entails.eval a c5897 := h 5896 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8621 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8621 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8620, some c675, some c667, some c8438, some c682, some c5986, some c5961, some c5949, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8621 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8621 : lratChecker f8621 p8621 = .success := by decide +kernel
theorem unsat8621 : Unsatisfiable (PosFin 65) f8621 := by
  apply lratCheckerSound f8621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8621
  · intro a ha; simp [p8621] at ha; subst a; trivial
  · exact checked8621
theorem derived8621 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8621 := by
  apply localUnsat_implies_entails f8621 [c8620, c675, c667, c8438, c682, c5986, c5961, c5949] c8621 unsat8621 (by rfl) a
  have h0 : Entails.eval a c8620 := derived8620 a h
  have h1 : Entails.eval a c675 := h 674 (by decide)
  have h2 : Entails.eval a c667 := h 666 (by decide)
  have h3 : Entails.eval a c8438 := derived8438 a h
  have h4 : Entails.eval a c682 := h 681 (by decide)
  have h5 : Entails.eval a c5986 := h 5985 (by decide)
  have h6 : Entails.eval a c5961 := h 5960 (by decide)
  have h7 : Entails.eval a c5949 := h 5948 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8622 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8622 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5527, some c5528, some c5517, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8622 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8622 : lratChecker f8622 p8622 = .success := by decide +kernel
theorem unsat8622 : Unsatisfiable (PosFin 65) f8622 := by
  apply lratCheckerSound f8622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8622
  · intro a ha; simp [p8622] at ha; subst a; trivial
  · exact checked8622
theorem derived8622 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8622 := by
  apply localUnsat_implies_entails f8622 [c5527, c5528, c5517] c8622 unsat8622 (by rfl) a
  have h0 : Entails.eval a c5527 := h 5526 (by decide)
  have h1 : Entails.eval a c5528 := h 5527 (by decide)
  have h2 : Entails.eval a c5517 := h 5516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8623 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8623 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8621, some c8622, some c675, some c667, some c8438, some c5852, some c5585, some c8435, some c5834, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8623 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8623 : lratChecker f8623 p8623 = .success := by decide +kernel
theorem unsat8623 : Unsatisfiable (PosFin 65) f8623 := by
  apply lratCheckerSound f8623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8623
  · intro a ha; simp [p8623] at ha; subst a; trivial
  · exact checked8623
theorem derived8623 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8623 := by
  apply localUnsat_implies_entails f8623 [c8621, c8622, c675, c667, c8438, c5852, c5585, c8435, c5834] c8623 unsat8623 (by rfl) a
  have h0 : Entails.eval a c8621 := derived8621 a h
  have h1 : Entails.eval a c8622 := derived8622 a h
  have h2 : Entails.eval a c675 := h 674 (by decide)
  have h3 : Entails.eval a c667 := h 666 (by decide)
  have h4 : Entails.eval a c8438 := derived8438 a h
  have h5 : Entails.eval a c5852 := h 5851 (by decide)
  have h6 : Entails.eval a c5585 := h 5584 (by decide)
  have h7 : Entails.eval a c8435 := derived8435 a h
  have h8 : Entails.eval a c5834 := h 5833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8624 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨57, by decide⟩, false), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨18, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8624 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5504, some c133, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8624 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8624 : lratChecker f8624 p8624 = .success := by decide +kernel
theorem unsat8624 : Unsatisfiable (PosFin 65) f8624 := by
  apply lratCheckerSound f8624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8624
  · intro a ha; simp [p8624] at ha; subst a; trivial
  · exact checked8624
theorem derived8624 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8624 := by
  apply localUnsat_implies_entails f8624 [c5504, c133] c8624 unsat8624 (by rfl) a
  have h0 : Entails.eval a c5504 := h 5503 (by decide)
  have h1 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8625 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨64, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8625 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8610, some c8619, some c8623, some c8496, some c675, some c667, some c8580, some c685, some c661, some c698, some c676, some c682, some c8391, some c8505, some c8624, some c8512, some c8513, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8625 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8625 : lratChecker f8625 p8625 = .success := by decide +kernel
theorem unsat8625 : Unsatisfiable (PosFin 65) f8625 := by
  apply lratCheckerSound f8625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8625
  · intro a ha; simp [p8625] at ha; subst a; trivial
  · exact checked8625
theorem derived8625 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8625 := by
  apply localUnsat_implies_entails f8625 [c8610, c8619, c8623, c8496, c675, c667, c8580, c685, c661, c698, c676, c682, c8391, c8505, c8624, c8512, c8513] c8625 unsat8625 (by rfl) a
  have h0 : Entails.eval a c8610 := derived8610 a h
  have h1 : Entails.eval a c8619 := derived8619 a h
  have h2 : Entails.eval a c8623 := derived8623 a h
  have h3 : Entails.eval a c8496 := derived8496 a h
  have h4 : Entails.eval a c675 := h 674 (by decide)
  have h5 : Entails.eval a c667 := h 666 (by decide)
  have h6 : Entails.eval a c8580 := derived8580 a h
  have h7 : Entails.eval a c685 := h 684 (by decide)
  have h8 : Entails.eval a c661 := h 660 (by decide)
  have h9 : Entails.eval a c698 := h 697 (by decide)
  have h10 : Entails.eval a c676 := h 675 (by decide)
  have h11 : Entails.eval a c682 := h 681 (by decide)
  have h12 : Entails.eval a c8391 := derived8391 a h
  have h13 : Entails.eval a c8505 := derived8505 a h
  have h14 : Entails.eval a c8624 := derived8624 a h
  have h15 : Entails.eval a c8512 := derived8512 a h
  have h16 : Entails.eval a c8513 := derived8513 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8626 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8626 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c188, some c5389, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8626 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8626 : lratChecker f8626 p8626 = .success := by decide +kernel
theorem unsat8626 : Unsatisfiable (PosFin 65) f8626 := by
  apply lratCheckerSound f8626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8626
  · intro a ha; simp [p8626] at ha; subst a; trivial
  · exact checked8626
theorem derived8626 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8626 := by
  apply localUnsat_implies_entails f8626 [c188, c5389] c8626 unsat8626 (by rfl) a
  have h0 : Entails.eval a c188 := h 187 (by decide)
  have h1 : Entails.eval a c5389 := h 5388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8627 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8627 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8610, some c8619, some c8623, some c8496, some c667, some c675, some c682, some c8580, some c685, some c661, some c698, some c688, some c676, some c8626, some c8625, some c8269, some c8366, some c37, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8627 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8627 : lratChecker f8627 p8627 = .success := by decide +kernel
theorem unsat8627 : Unsatisfiable (PosFin 65) f8627 := by
  apply lratCheckerSound f8627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8627
  · intro a ha; simp [p8627] at ha; subst a; trivial
  · exact checked8627
theorem derived8627 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8627 := by
  apply localUnsat_implies_entails f8627 [c8610, c8619, c8623, c8496, c667, c675, c682, c8580, c685, c661, c698, c688, c676, c8626, c8625, c8269, c8366, c37] c8627 unsat8627 (by rfl) a
  have h0 : Entails.eval a c8610 := derived8610 a h
  have h1 : Entails.eval a c8619 := derived8619 a h
  have h2 : Entails.eval a c8623 := derived8623 a h
  have h3 : Entails.eval a c8496 := derived8496 a h
  have h4 : Entails.eval a c667 := h 666 (by decide)
  have h5 : Entails.eval a c675 := h 674 (by decide)
  have h6 : Entails.eval a c682 := h 681 (by decide)
  have h7 : Entails.eval a c8580 := derived8580 a h
  have h8 : Entails.eval a c685 := h 684 (by decide)
  have h9 : Entails.eval a c661 := h 660 (by decide)
  have h10 : Entails.eval a c698 := h 697 (by decide)
  have h11 : Entails.eval a c688 := h 687 (by decide)
  have h12 : Entails.eval a c676 := h 675 (by decide)
  have h13 : Entails.eval a c8626 := derived8626 a h
  have h14 : Entails.eval a c8625 := derived8625 a h
  have h15 : Entails.eval a c8269 := derived8269 a h
  have h16 : Entails.eval a c8366 := derived8366 a h
  have h17 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8628 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8628 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8610, some c8619, some c8623, some c8496, some c8580, some c675, some c667, some c685, some c676, some c8627, some c8521, some c5852, some c6020, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8628 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8628 : lratChecker f8628 p8628 = .success := by decide +kernel
theorem unsat8628 : Unsatisfiable (PosFin 65) f8628 := by
  apply lratCheckerSound f8628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8628
  · intro a ha; simp [p8628] at ha; subst a; trivial
  · exact checked8628
theorem derived8628 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8628 := by
  apply localUnsat_implies_entails f8628 [c8610, c8619, c8623, c8496, c8580, c675, c667, c685, c676, c8627, c8521, c5852, c6020] c8628 unsat8628 (by rfl) a
  have h0 : Entails.eval a c8610 := derived8610 a h
  have h1 : Entails.eval a c8619 := derived8619 a h
  have h2 : Entails.eval a c8623 := derived8623 a h
  have h3 : Entails.eval a c8496 := derived8496 a h
  have h4 : Entails.eval a c8580 := derived8580 a h
  have h5 : Entails.eval a c675 := h 674 (by decide)
  have h6 : Entails.eval a c667 := h 666 (by decide)
  have h7 : Entails.eval a c685 := h 684 (by decide)
  have h8 : Entails.eval a c676 := h 675 (by decide)
  have h9 : Entails.eval a c8627 := derived8627 a h
  have h10 : Entails.eval a c8521 := derived8521 a h
  have h11 : Entails.eval a c5852 := h 5851 (by decide)
  have h12 : Entails.eval a c6020 := h 6019 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8629 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨27, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8629 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8426, some c8490, some c8496, some c702, some c664, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8629 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8629 : lratChecker f8629 p8629 = .success := by decide +kernel
theorem unsat8629 : Unsatisfiable (PosFin 65) f8629 := by
  apply lratCheckerSound f8629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8629
  · intro a ha; simp [p8629] at ha; subst a; trivial
  · exact checked8629
theorem derived8629 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8629 := by
  apply localUnsat_implies_entails f8629 [c8426, c8490, c8496, c702, c664] c8629 unsat8629 (by rfl) a
  have h0 : Entails.eval a c8426 := derived8426 a h
  have h1 : Entails.eval a c8490 := derived8490 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c702 := h 701 (by decide)
  have h4 : Entails.eval a c664 := h 663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8630 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8630 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8629, some c664, some c659, some c671, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8630 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8630 : lratChecker f8630 p8630 = .success := by decide +kernel
theorem unsat8630 : Unsatisfiable (PosFin 65) f8630 := by
  apply lratCheckerSound f8630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8630
  · intro a ha; simp [p8630] at ha; subst a; trivial
  · exact checked8630
theorem derived8630 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8630 := by
  apply localUnsat_implies_entails f8630 [c8629, c664, c659, c671] c8630 unsat8630 (by rfl) a
  have h0 : Entails.eval a c8629 := derived8629 a h
  have h1 : Entails.eval a c664 := h 663 (by decide)
  have h2 : Entails.eval a c659 := h 658 (by decide)
  have h3 : Entails.eval a c671 := h 670 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8631 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨57, by decide⟩, false), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8631 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1232, some c1234, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8631 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8631 : lratChecker f8631 p8631 = .success := by decide +kernel
theorem unsat8631 : Unsatisfiable (PosFin 65) f8631 := by
  apply lratCheckerSound f8631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8631
  · intro a ha; simp [p8631] at ha; subst a; trivial
  · exact checked8631
theorem derived8631 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8631 := by
  apply localUnsat_implies_entails f8631 [c1232, c1234] c8631 unsat8631 (by rfl) a
  have h0 : Entails.eval a c1232 := h 1231 (by decide)
  have h1 : Entails.eval a c1234 := h 1233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8632 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8632 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c225, some c235, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8632 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8632 : lratChecker f8632 p8632 = .success := by decide +kernel
theorem unsat8632 : Unsatisfiable (PosFin 65) f8632 := by
  apply lratCheckerSound f8632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8632
  · intro a ha; simp [p8632] at ha; subst a; trivial
  · exact checked8632
theorem derived8632 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8632 := by
  apply localUnsat_implies_entails f8632 [c225, c235] c8632 unsat8632 (by rfl) a
  have h0 : Entails.eval a c225 := h 224 (by decide)
  have h1 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8633 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8633 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8610, some c1233, some c1232, some c1419, some c1174, some c26, some c13, some c6563, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8633 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8633 : lratChecker f8633 p8633 = .success := by decide +kernel
theorem unsat8633 : Unsatisfiable (PosFin 65) f8633 := by
  apply lratCheckerSound f8633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8633
  · intro a ha; simp [p8633] at ha; subst a; trivial
  · exact checked8633
theorem derived8633 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8633 := by
  apply localUnsat_implies_entails f8633 [c8610, c1233, c1232, c1419, c1174, c26, c13, c6563] c8633 unsat8633 (by rfl) a
  have h0 : Entails.eval a c8610 := derived8610 a h
  have h1 : Entails.eval a c1233 := h 1232 (by decide)
  have h2 : Entails.eval a c1232 := h 1231 (by decide)
  have h3 : Entails.eval a c1419 := h 1418 (by decide)
  have h4 : Entails.eval a c1174 := h 1173 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c6563 := h 6562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8634 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨30, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8634 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8505, some c8421, some c8632, some c8633, some c4872, some c4862, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8634 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8634 : lratChecker f8634 p8634 = .success := by decide +kernel
theorem unsat8634 : Unsatisfiable (PosFin 65) f8634 := by
  apply lratCheckerSound f8634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8634
  · intro a ha; simp [p8634] at ha; subst a; trivial
  · exact checked8634
theorem derived8634 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8634 := by
  apply localUnsat_implies_entails f8634 [c8505, c8421, c8632, c8633, c4872, c4862] c8634 unsat8634 (by rfl) a
  have h0 : Entails.eval a c8505 := derived8505 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8632 := derived8632 a h
  have h3 : Entails.eval a c8633 := derived8633 a h
  have h4 : Entails.eval a c4872 := h 4871 (by decide)
  have h5 : Entails.eval a c4862 := h 4861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8635 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8635 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8269, some c8366, some c8472, some c25, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8635 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8635 : lratChecker f8635 p8635 = .success := by decide +kernel
theorem unsat8635 : Unsatisfiable (PosFin 65) f8635 := by
  apply lratCheckerSound f8635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8635
  · intro a ha; simp [p8635] at ha; subst a; trivial
  · exact checked8635
theorem derived8635 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8635 := by
  apply localUnsat_implies_entails f8635 [c7994, c8269, c8366, c8472, c25] c8635 unsat8635 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8366 := derived8366 a h
  have h3 : Entails.eval a c8472 := derived8472 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8636 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8636 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1403, some c1430, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8636 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8636 : lratChecker f8636 p8636 = .success := by decide +kernel
theorem unsat8636 : Unsatisfiable (PosFin 65) f8636 := by
  apply lratCheckerSound f8636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8636
  · intro a ha; simp [p8636] at ha; subst a; trivial
  · exact checked8636
theorem derived8636 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8636 := by
  apply localUnsat_implies_entails f8636 [c1403, c1430] c8636 unsat8636 (by rfl) a
  have h0 : Entails.eval a c1403 := h 1402 (by decide)
  have h1 : Entails.eval a c1430 := h 1429 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8637 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, false), (⟨64, by decide⟩, true), (⟨24, by decide⟩, false), (⟨30, by decide⟩, true), (⟨21, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8637 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8512, some c8636, some c8487, some c302, some c294, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8637 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8637 : lratChecker f8637 p8637 = .success := by decide +kernel
theorem unsat8637 : Unsatisfiable (PosFin 65) f8637 := by
  apply lratCheckerSound f8637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8637
  · intro a ha; simp [p8637] at ha; subst a; trivial
  · exact checked8637
theorem derived8637 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8637 := by
  apply localUnsat_implies_entails f8637 [c8512, c8636, c8487, c302, c294] c8637 unsat8637 (by rfl) a
  have h0 : Entails.eval a c8512 := derived8512 a h
  have h1 : Entails.eval a c8636 := derived8636 a h
  have h2 : Entails.eval a c8487 := derived8487 a h
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8638 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8638 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8628, some c8629, some c8635, some c8630, some c8580, some c8583, some c685, some c8510, some c668, some c692, some c658, some c8505, some c8610, some c8634, some c8637, some c8624, some c188, some c5468, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8638 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8638 : lratChecker f8638 p8638 = .success := by decide +kernel
theorem unsat8638 : Unsatisfiable (PosFin 65) f8638 := by
  apply lratCheckerSound f8638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8638
  · intro a ha; simp [p8638] at ha; subst a; trivial
  · exact checked8638
theorem derived8638 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8638 := by
  apply localUnsat_implies_entails f8638 [c8421, c8628, c8629, c8635, c8630, c8580, c8583, c685, c8510, c668, c692, c658, c8505, c8610, c8634, c8637, c8624, c188, c5468] c8638 unsat8638 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8628 := derived8628 a h
  have h2 : Entails.eval a c8629 := derived8629 a h
  have h3 : Entails.eval a c8635 := derived8635 a h
  have h4 : Entails.eval a c8630 := derived8630 a h
  have h5 : Entails.eval a c8580 := derived8580 a h
  have h6 : Entails.eval a c8583 := derived8583 a h
  have h7 : Entails.eval a c685 := h 684 (by decide)
  have h8 : Entails.eval a c8510 := derived8510 a h
  have h9 : Entails.eval a c668 := h 667 (by decide)
  have h10 : Entails.eval a c692 := h 691 (by decide)
  have h11 : Entails.eval a c658 := h 657 (by decide)
  have h12 : Entails.eval a c8505 := derived8505 a h
  have h13 : Entails.eval a c8610 := derived8610 a h
  have h14 : Entails.eval a c8634 := derived8634 a h
  have h15 : Entails.eval a c8637 := derived8637 a h
  have h16 : Entails.eval a c8624 := derived8624 a h
  have h17 : Entails.eval a c188 := h 187 (by decide)
  have h18 : Entails.eval a c5468 := h 5467 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8639 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8639 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8610, some c8628, some c8629, some c8630, some c8580, some c8583, some c692, some c685, some c658, some c668, some c8638, some c6026, some c6027, some c6014, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8639 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8639 : lratChecker f8639 p8639 = .success := by decide +kernel
theorem unsat8639 : Unsatisfiable (PosFin 65) f8639 := by
  apply lratCheckerSound f8639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8639
  · intro a ha; simp [p8639] at ha; subst a; trivial
  · exact checked8639
theorem derived8639 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8639 := by
  apply localUnsat_implies_entails f8639 [c8610, c8628, c8629, c8630, c8580, c8583, c692, c685, c658, c668, c8638, c6026, c6027, c6014] c8639 unsat8639 (by rfl) a
  have h0 : Entails.eval a c8610 := derived8610 a h
  have h1 : Entails.eval a c8628 := derived8628 a h
  have h2 : Entails.eval a c8629 := derived8629 a h
  have h3 : Entails.eval a c8630 := derived8630 a h
  have h4 : Entails.eval a c8580 := derived8580 a h
  have h5 : Entails.eval a c8583 := derived8583 a h
  have h6 : Entails.eval a c692 := h 691 (by decide)
  have h7 : Entails.eval a c685 := h 684 (by decide)
  have h8 : Entails.eval a c658 := h 657 (by decide)
  have h9 : Entails.eval a c668 := h 667 (by decide)
  have h10 : Entails.eval a c8638 := derived8638 a h
  have h11 : Entails.eval a c6026 := h 6025 (by decide)
  have h12 : Entails.eval a c6027 := h 6026 (by decide)
  have h13 : Entails.eval a c6014 := h 6013 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8640 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8640 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5555, some c5514, some c5544, some c5947, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8640 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8640 : lratChecker f8640 p8640 = .success := by decide +kernel
theorem unsat8640 : Unsatisfiable (PosFin 65) f8640 := by
  apply lratCheckerSound f8640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8640
  · intro a ha; simp [p8640] at ha; subst a; trivial
  · exact checked8640
theorem derived8640 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8640 := by
  apply localUnsat_implies_entails f8640 [c5555, c5514, c5544, c5947] c8640 unsat8640 (by rfl) a
  have h0 : Entails.eval a c5555 := h 5554 (by decide)
  have h1 : Entails.eval a c5514 := h 5513 (by decide)
  have h2 : Entails.eval a c5544 := h 5543 (by decide)
  have h3 : Entails.eval a c5947 := h 5946 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8641 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8641 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8640, some c5702, some c5727, some c5609, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8641 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8641 : lratChecker f8641 p8641 = .success := by decide +kernel
theorem unsat8641 : Unsatisfiable (PosFin 65) f8641 := by
  apply lratCheckerSound f8641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8641
  · intro a ha; simp [p8641] at ha; subst a; trivial
  · exact checked8641
theorem derived8641 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8641 := by
  apply localUnsat_implies_entails f8641 [c8640, c5702, c5727, c5609] c8641 unsat8641 (by rfl) a
  have h0 : Entails.eval a c8640 := derived8640 a h
  have h1 : Entails.eval a c5702 := h 5701 (by decide)
  have h2 : Entails.eval a c5727 := h 5726 (by decide)
  have h3 : Entails.eval a c5609 := h 5608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8642 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8642 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8640, some c17, some c8641, some c48, some c6561, some c6605, some c6616, some c104, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8642 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8642 : lratChecker f8642 p8642 = .success := by decide +kernel
theorem unsat8642 : Unsatisfiable (PosFin 65) f8642 := by
  apply lratCheckerSound f8642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8642
  · intro a ha; simp [p8642] at ha; subst a; trivial
  · exact checked8642
theorem derived8642 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8642 := by
  apply localUnsat_implies_entails f8642 [c8640, c17, c8641, c48, c6561, c6605, c6616, c104] c8642 unsat8642 (by rfl) a
  have h0 : Entails.eval a c8640 := derived8640 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c8641 := derived8641 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c6561 := h 6560 (by decide)
  have h5 : Entails.eval a c6605 := h 6604 (by decide)
  have h6 : Entails.eval a c6616 := h 6615 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8643 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨35, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8643 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c48, some c6561, some c6779, some c6767, some c102, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8643 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8643 : lratChecker f8643 p8643 = .success := by decide +kernel
theorem unsat8643 : Unsatisfiable (PosFin 65) f8643 := by
  apply lratCheckerSound f8643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8643
  · intro a ha; simp [p8643] at ha; subst a; trivial
  · exact checked8643
theorem derived8643 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8643 := by
  apply localUnsat_implies_entails f8643 [c48, c6561, c6779, c6767, c102] c8643 unsat8643 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c6561 := h 6560 (by decide)
  have h2 : Entails.eval a c6779 := h 6778 (by decide)
  have h3 : Entails.eval a c6767 := h 6766 (by decide)
  have h4 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8644 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8644 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5574, some c5595, some c5748, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8644 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8644 : lratChecker f8644 p8644 = .success := by decide +kernel
theorem unsat8644 : Unsatisfiable (PosFin 65) f8644 := by
  apply lratCheckerSound f8644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8644
  · intro a ha; simp [p8644] at ha; subst a; trivial
  · exact checked8644
theorem derived8644 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8644 := by
  apply localUnsat_implies_entails f8644 [c5574, c5595, c5748] c8644 unsat8644 (by rfl) a
  have h0 : Entails.eval a c5574 := h 5573 (by decide)
  have h1 : Entails.eval a c5595 := h 5594 (by decide)
  have h2 : Entails.eval a c5748 := h 5747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8645 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8645 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6595, some c6561, some c6578, some c7084, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p8645 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8645 : lratChecker f8645 p8645 = .success := by decide +kernel
theorem unsat8645 : Unsatisfiable (PosFin 65) f8645 := by
  apply lratCheckerSound f8645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8645
  · intro a ha; simp [p8645] at ha; subst a; trivial
  · exact checked8645
theorem derived8645 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8645 := by
  apply localUnsat_implies_entails f8645 [c6595, c6561, c6578, c7084] c8645 unsat8645 (by rfl) a
  have h0 : Entails.eval a c6595 := h 6594 (by decide)
  have h1 : Entails.eval a c6561 := h 6560 (by decide)
  have h2 : Entails.eval a c6578 := h 6577 (by decide)
  have h3 : Entails.eval a c7084 := h 7083 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8646 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8646 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8610, some c8639, some c8642, some c30, some c8643, some c8644, some c17, some c8645, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8646 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8646 : lratChecker f8646 p8646 = .success := by decide +kernel
theorem unsat8646 : Unsatisfiable (PosFin 65) f8646 := by
  apply lratCheckerSound f8646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8646
  · intro a ha; simp [p8646] at ha; subst a; trivial
  · exact checked8646
theorem derived8646 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8646 := by
  apply localUnsat_implies_entails f8646 [c8610, c8639, c8642, c30, c8643, c8644, c17, c8645] c8646 unsat8646 (by rfl) a
  have h0 : Entails.eval a c8610 := derived8610 a h
  have h1 : Entails.eval a c8639 := derived8639 a h
  have h2 : Entails.eval a c8642 := derived8642 a h
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c8643 := derived8643 a h
  have h5 : Entails.eval a c8644 := derived8644 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c8645 := derived8645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8647 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8647 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8629, some c8496, some c654, some c684, some c8435, some c680, some c653, some c8490, some c8426, some c8646, some c8610, some c8421, some c1179, some c630, some c580, some c8611, some c5872, some c4884, some c297, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8647 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8647 : lratChecker f8647 p8647 = .success := by decide +kernel
theorem unsat8647 : Unsatisfiable (PosFin 65) f8647 := by
  apply lratCheckerSound f8647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8647
  · intro a ha; simp [p8647] at ha; subst a; trivial
  · exact checked8647
theorem derived8647 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8647 := by
  apply localUnsat_implies_entails f8647 [c8629, c8496, c654, c684, c8435, c680, c653, c8490, c8426, c8646, c8610, c8421, c1179, c630, c580, c8611, c5872, c4884, c297] c8647 unsat8647 (by rfl) a
  have h0 : Entails.eval a c8629 := derived8629 a h
  have h1 : Entails.eval a c8496 := derived8496 a h
  have h2 : Entails.eval a c654 := h 653 (by decide)
  have h3 : Entails.eval a c684 := h 683 (by decide)
  have h4 : Entails.eval a c8435 := derived8435 a h
  have h5 : Entails.eval a c680 := h 679 (by decide)
  have h6 : Entails.eval a c653 := h 652 (by decide)
  have h7 : Entails.eval a c8490 := derived8490 a h
  have h8 : Entails.eval a c8426 := derived8426 a h
  have h9 : Entails.eval a c8646 := derived8646 a h
  have h10 : Entails.eval a c8610 := derived8610 a h
  have h11 : Entails.eval a c8421 := derived8421 a h
  have h12 : Entails.eval a c1179 := h 1178 (by decide)
  have h13 : Entails.eval a c630 := h 629 (by decide)
  have h14 : Entails.eval a c580 := h 579 (by decide)
  have h15 : Entails.eval a c8611 := derived8611 a h
  have h16 : Entails.eval a c5872 := h 5871 (by decide)
  have h17 : Entails.eval a c4884 := h 4883 (by decide)
  have h18 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8648 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8648 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8610, some c8426, some c8490, some c8496, some c8629, some c702, some c703, some c706, some c654, some c8436, some c8647, some c581, some c5730, some c6017, some c5731, some c5868, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8648 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8648 : lratChecker f8648 p8648 = .success := by decide +kernel
theorem unsat8648 : Unsatisfiable (PosFin 65) f8648 := by
  apply lratCheckerSound f8648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8648
  · intro a ha; simp [p8648] at ha; subst a; trivial
  · exact checked8648
theorem derived8648 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8648 := by
  apply localUnsat_implies_entails f8648 [c8610, c8426, c8490, c8496, c8629, c702, c703, c706, c654, c8436, c8647, c581, c5730, c6017, c5731, c5868] c8648 unsat8648 (by rfl) a
  have h0 : Entails.eval a c8610 := derived8610 a h
  have h1 : Entails.eval a c8426 := derived8426 a h
  have h2 : Entails.eval a c8490 := derived8490 a h
  have h3 : Entails.eval a c8496 := derived8496 a h
  have h4 : Entails.eval a c8629 := derived8629 a h
  have h5 : Entails.eval a c702 := h 701 (by decide)
  have h6 : Entails.eval a c703 := h 702 (by decide)
  have h7 : Entails.eval a c706 := h 705 (by decide)
  have h8 : Entails.eval a c654 := h 653 (by decide)
  have h9 : Entails.eval a c8436 := derived8436 a h
  have h10 : Entails.eval a c8647 := derived8647 a h
  have h11 : Entails.eval a c581 := h 580 (by decide)
  have h12 : Entails.eval a c5730 := h 5729 (by decide)
  have h13 : Entails.eval a c6017 := h 6016 (by decide)
  have h14 : Entails.eval a c5731 := h 5730 (by decide)
  have h15 : Entails.eval a c5868 := h 5867 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8649 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8649 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8438, some c8630, some c8435, some c8436, some c579, some c8613, some c692, some c5996, some c6000, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8649 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8649 : lratChecker f8649 p8649 = .success := by decide +kernel
theorem unsat8649 : Unsatisfiable (PosFin 65) f8649 := by
  apply lratCheckerSound f8649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8649
  · intro a ha; simp [p8649] at ha; subst a; trivial
  · exact checked8649
theorem derived8649 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8649 := by
  apply localUnsat_implies_entails f8649 [c8438, c8630, c8435, c8436, c579, c8613, c692, c5996, c6000] c8649 unsat8649 (by rfl) a
  have h0 : Entails.eval a c8438 := derived8438 a h
  have h1 : Entails.eval a c8630 := derived8630 a h
  have h2 : Entails.eval a c8435 := derived8435 a h
  have h3 : Entails.eval a c8436 := derived8436 a h
  have h4 : Entails.eval a c579 := h 578 (by decide)
  have h5 : Entails.eval a c8613 := derived8613 a h
  have h6 : Entails.eval a c692 := h 691 (by decide)
  have h7 : Entails.eval a c5996 := h 5995 (by decide)
  have h8 : Entails.eval a c6000 := h 5999 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8650 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8650 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8582, some c1223, some c1449, some c310, some c1215, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8650 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8650 : lratChecker f8650 p8650 = .success := by decide +kernel
theorem unsat8650 : Unsatisfiable (PosFin 65) f8650 := by
  apply lratCheckerSound f8650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8650
  · intro a ha; simp [p8650] at ha; subst a; trivial
  · exact checked8650
theorem derived8650 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8650 := by
  apply localUnsat_implies_entails f8650 [c8582, c1223, c1449, c310, c1215] c8650 unsat8650 (by rfl) a
  have h0 : Entails.eval a c8582 := derived8582 a h
  have h1 : Entails.eval a c1223 := h 1222 (by decide)
  have h2 : Entails.eval a c1449 := h 1448 (by decide)
  have h3 : Entails.eval a c310 := h 309 (by decide)
  have h4 : Entails.eval a c1215 := h 1214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8650

end CochromaticTwenty.Certificates.FixedCore0
