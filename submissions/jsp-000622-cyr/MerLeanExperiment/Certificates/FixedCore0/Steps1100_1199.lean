import MerLeanExperiment.Certificates.FixedCore0.Steps1000_1099

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8651 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8651 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8648, some c8646, some c8610, some c8421, some c8649, some c8580, some c8650, some c8583, some c690, some c697, some c685, some c8510, some c1125, some c1179, some c4429, some c4701, some c211, some c210, some c348, some c272, some c222, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8651 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8651 : lratChecker f8651 p8651 = .success := by decide +kernel
theorem unsat8651 : Unsatisfiable (PosFin 65) f8651 := by
  apply lratCheckerSound f8651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8651
  · intro a ha; simp [p8651] at ha; subst a; trivial
  · exact checked8651
theorem derived8651 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8651 := by
  apply localUnsat_implies_entails f8651 [c8648, c8646, c8610, c8421, c8649, c8580, c8650, c8583, c690, c697, c685, c8510, c1125, c1179, c4429, c4701, c211, c210, c348, c272, c222] c8651 unsat8651 (by rfl) a
  have h0 : Entails.eval a c8648 := derived8648 a h
  have h1 : Entails.eval a c8646 := derived8646 a h
  have h2 : Entails.eval a c8610 := derived8610 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8649 := derived8649 a h
  have h5 : Entails.eval a c8580 := derived8580 a h
  have h6 : Entails.eval a c8650 := derived8650 a h
  have h7 : Entails.eval a c8583 := derived8583 a h
  have h8 : Entails.eval a c690 := h 689 (by decide)
  have h9 : Entails.eval a c697 := h 696 (by decide)
  have h10 : Entails.eval a c685 := h 684 (by decide)
  have h11 : Entails.eval a c8510 := derived8510 a h
  have h12 : Entails.eval a c1125 := h 1124 (by decide)
  have h13 : Entails.eval a c1179 := h 1178 (by decide)
  have h14 : Entails.eval a c4429 := h 4428 (by decide)
  have h15 : Entails.eval a c4701 := h 4700 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c272 := h 271 (by decide)
  have h20 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8652 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8652 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8651, some c8648, some c8646, some c8610, some c8421, some c8438, some c8630, some c8435, some c8436, some c705, some c8613, some c8600, some c571, some c5861, some c703, some c5928, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8652 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8652 : lratChecker f8652 p8652 = .success := by decide +kernel
theorem unsat8652 : Unsatisfiable (PosFin 65) f8652 := by
  apply lratCheckerSound f8652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8652
  · intro a ha; simp [p8652] at ha; subst a; trivial
  · exact checked8652
theorem derived8652 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8652 := by
  apply localUnsat_implies_entails f8652 [c8651, c8648, c8646, c8610, c8421, c8438, c8630, c8435, c8436, c705, c8613, c8600, c571, c5861, c703, c5928] c8652 unsat8652 (by rfl) a
  have h0 : Entails.eval a c8651 := derived8651 a h
  have h1 : Entails.eval a c8648 := derived8648 a h
  have h2 : Entails.eval a c8646 := derived8646 a h
  have h3 : Entails.eval a c8610 := derived8610 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c8438 := derived8438 a h
  have h6 : Entails.eval a c8630 := derived8630 a h
  have h7 : Entails.eval a c8435 := derived8435 a h
  have h8 : Entails.eval a c8436 := derived8436 a h
  have h9 : Entails.eval a c705 := h 704 (by decide)
  have h10 : Entails.eval a c8613 := derived8613 a h
  have h11 : Entails.eval a c8600 := derived8600 a h
  have h12 : Entails.eval a c571 := h 570 (by decide)
  have h13 : Entails.eval a c5861 := h 5860 (by decide)
  have h14 : Entails.eval a c703 := h 702 (by decide)
  have h15 : Entails.eval a c5928 := h 5927 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8653 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8653 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8646, some c8421, some c8648, some c8651, some c8652, some c8580, some c8600, some c8583, some c690, some c697, some c658, some c657, some c671, some c1132, some c627, some c577, some c1194, some c4711, some c4441, some c345, some c274, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8653 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8653 : lratChecker f8653 p8653 = .success := by decide +kernel
theorem unsat8653 : Unsatisfiable (PosFin 65) f8653 := by
  apply lratCheckerSound f8653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8653
  · intro a ha; simp [p8653] at ha; subst a; trivial
  · exact checked8653
theorem derived8653 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8653 := by
  apply localUnsat_implies_entails f8653 [c8646, c8421, c8648, c8651, c8652, c8580, c8600, c8583, c690, c697, c658, c657, c671, c1132, c627, c577, c1194, c4711, c4441, c345, c274] c8653 unsat8653 (by rfl) a
  have h0 : Entails.eval a c8646 := derived8646 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8648 := derived8648 a h
  have h3 : Entails.eval a c8651 := derived8651 a h
  have h4 : Entails.eval a c8652 := derived8652 a h
  have h5 : Entails.eval a c8580 := derived8580 a h
  have h6 : Entails.eval a c8600 := derived8600 a h
  have h7 : Entails.eval a c8583 := derived8583 a h
  have h8 : Entails.eval a c690 := h 689 (by decide)
  have h9 : Entails.eval a c697 := h 696 (by decide)
  have h10 : Entails.eval a c658 := h 657 (by decide)
  have h11 : Entails.eval a c657 := h 656 (by decide)
  have h12 : Entails.eval a c671 := h 670 (by decide)
  have h13 : Entails.eval a c1132 := h 1131 (by decide)
  have h14 : Entails.eval a c627 := h 626 (by decide)
  have h15 : Entails.eval a c577 := h 576 (by decide)
  have h16 : Entails.eval a c1194 := h 1193 (by decide)
  have h17 : Entails.eval a c4711 := h 4710 (by decide)
  have h18 : Entails.eval a c4441 := h 4440 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8654 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8654 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5988, some c8590, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8654 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8654 : lratChecker f8654 p8654 = .success := by decide +kernel
theorem unsat8654 : Unsatisfiable (PosFin 65) f8654 := by
  apply lratCheckerSound f8654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8654
  · intro a ha; simp [p8654] at ha; subst a; trivial
  · exact checked8654
theorem derived8654 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8654 := by
  apply localUnsat_implies_entails f8654 [c5988, c8590] c8654 unsat8654 (by rfl) a
  have h0 : Entails.eval a c5988 := h 5987 (by decide)
  have h1 : Entails.eval a c8590 := derived8590 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8655 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8655 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5811, some c5965, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8655 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8655 : lratChecker f8655 p8655 = .success := by decide +kernel
theorem unsat8655 : Unsatisfiable (PosFin 65) f8655 := by
  apply lratCheckerSound f8655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8655
  · intro a ha; simp [p8655] at ha; subst a; trivial
  · exact checked8655
theorem derived8655 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8655 := by
  apply localUnsat_implies_entails f8655 [c5811, c5965] c8655 unsat8655 (by rfl) a
  have h0 : Entails.eval a c5811 := h 5810 (by decide)
  have h1 : Entails.eval a c5965 := h 5964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8656 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨32, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8656 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8544, some c4898, some c4865, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8656 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8656 : lratChecker f8656 p8656 = .success := by decide +kernel
theorem unsat8656 : Unsatisfiable (PosFin 65) f8656 := by
  apply lratCheckerSound f8656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8656
  · intro a ha; simp [p8656] at ha; subst a; trivial
  · exact checked8656
theorem derived8656 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8656 := by
  apply localUnsat_implies_entails f8656 [c8544, c4898, c4865] c8656 unsat8656 (by rfl) a
  have h0 : Entails.eval a c8544 := derived8544 a h
  have h1 : Entails.eval a c4898 := h 4897 (by decide)
  have h2 : Entails.eval a c4865 := h 4864 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8657 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8657 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8654, some c8655, some c8596, some c8656, some c910, some c4874, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8657 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8657 : lratChecker f8657 p8657 = .success := by decide +kernel
theorem unsat8657 : Unsatisfiable (PosFin 65) f8657 := by
  apply lratCheckerSound f8657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8657
  · intro a ha; simp [p8657] at ha; subst a; trivial
  · exact checked8657
theorem derived8657 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8657 := by
  apply localUnsat_implies_entails f8657 [c8654, c8655, c8596, c8656, c910, c4874] c8657 unsat8657 (by rfl) a
  have h0 : Entails.eval a c8654 := derived8654 a h
  have h1 : Entails.eval a c8655 := derived8655 a h
  have h2 : Entails.eval a c8596 := derived8596 a h
  have h3 : Entails.eval a c8656 := derived8656 a h
  have h4 : Entails.eval a c910 := h 909 (by decide)
  have h5 : Entails.eval a c4874 := h 4873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8658 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8658 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5541, some c5551, some c5942, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8658 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8658 : lratChecker f8658 p8658 = .success := by decide +kernel
theorem unsat8658 : Unsatisfiable (PosFin 65) f8658 := by
  apply lratCheckerSound f8658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8658
  · intro a ha; simp [p8658] at ha; subst a; trivial
  · exact checked8658
theorem derived8658 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8658 := by
  apply localUnsat_implies_entails f8658 [c5541, c5551, c5942] c8658 unsat8658 (by rfl) a
  have h0 : Entails.eval a c5541 := h 5540 (by decide)
  have h1 : Entails.eval a c5551 := h 5550 (by decide)
  have h2 : Entails.eval a c5942 := h 5941 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8659 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8659 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1224, some c8607, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8659 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8659 : lratChecker f8659 p8659 = .success := by decide +kernel
theorem unsat8659 : Unsatisfiable (PosFin 65) f8659 := by
  apply lratCheckerSound f8659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8659
  · intro a ha; simp [p8659] at ha; subst a; trivial
  · exact checked8659
theorem derived8659 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8659 := by
  apply localUnsat_implies_entails f8659 [c1224, c8607] c8659 unsat8659 (by rfl) a
  have h0 : Entails.eval a c1224 := h 1223 (by decide)
  have h1 : Entails.eval a c8607 := derived8607 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8660 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8660 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8604, some c8528, some c8534, some c909, some c935, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8660 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8660 : lratChecker f8660 p8660 = .success := by decide +kernel
theorem unsat8660 : Unsatisfiable (PosFin 65) f8660 := by
  apply lratCheckerSound f8660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8660
  · intro a ha; simp [p8660] at ha; subst a; trivial
  · exact checked8660
theorem derived8660 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8660 := by
  apply localUnsat_implies_entails f8660 [c8604, c8528, c8534, c909, c935] c8660 unsat8660 (by rfl) a
  have h0 : Entails.eval a c8604 := derived8604 a h
  have h1 : Entails.eval a c8528 := derived8528 a h
  have h2 : Entails.eval a c8534 := derived8534 a h
  have h3 : Entails.eval a c909 := h 908 (by decide)
  have h4 : Entails.eval a c935 := h 934 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8661 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8661 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8657, some c8658, some c8659, some c8660, some c8269, some c5559, some c5545, some c5954, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8661 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8661 : lratChecker f8661 p8661 = .success := by decide +kernel
theorem unsat8661 : Unsatisfiable (PosFin 65) f8661 := by
  apply lratCheckerSound f8661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8661
  · intro a ha; simp [p8661] at ha; subst a; trivial
  · exact checked8661
theorem derived8661 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8661 := by
  apply localUnsat_implies_entails f8661 [c8657, c8658, c8659, c8660, c8269, c5559, c5545, c5954] c8661 unsat8661 (by rfl) a
  have h0 : Entails.eval a c8657 := derived8657 a h
  have h1 : Entails.eval a c8658 := derived8658 a h
  have h2 : Entails.eval a c8659 := derived8659 a h
  have h3 : Entails.eval a c8660 := derived8660 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c5559 := h 5558 (by decide)
  have h6 : Entails.eval a c5545 := h 5544 (by decide)
  have h7 : Entails.eval a c5954 := h 5953 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8662 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8662 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8656, some c927, some c4881, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8662 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8662 : lratChecker f8662 p8662 = .success := by decide +kernel
theorem unsat8662 : Unsatisfiable (PosFin 65) f8662 := by
  apply lratCheckerSound f8662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8662
  · intro a ha; simp [p8662] at ha; subst a; trivial
  · exact checked8662
theorem derived8662 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8662 := by
  apply localUnsat_implies_entails f8662 [c8656, c927, c4881] c8662 unsat8662 (by rfl) a
  have h0 : Entails.eval a c8656 := derived8656 a h
  have h1 : Entails.eval a c927 := h 926 (by decide)
  have h2 : Entails.eval a c4881 := h 4880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8663 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8663 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8654, some c8655, some c8596, some c8662, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8663 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8663 : lratChecker f8663 p8663 = .success := by decide +kernel
theorem unsat8663 : Unsatisfiable (PosFin 65) f8663 := by
  apply lratCheckerSound f8663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8663
  · intro a ha; simp [p8663] at ha; subst a; trivial
  · exact checked8663
theorem derived8663 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8663 := by
  apply localUnsat_implies_entails f8663 [c8654, c8655, c8596, c8662] c8663 unsat8663 (by rfl) a
  have h0 : Entails.eval a c8654 := derived8654 a h
  have h1 : Entails.eval a c8655 := derived8655 a h
  have h2 : Entails.eval a c8596 := derived8596 a h
  have h3 : Entails.eval a c8662 := derived8662 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8664 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨35, by decide⟩, false), (⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8664 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c109, some c104, some c107, some c110, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8664 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8664 : lratChecker f8664 p8664 = .success := by decide +kernel
theorem unsat8664 : Unsatisfiable (PosFin 65) f8664 := by
  apply lratCheckerSound f8664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8664
  · intro a ha; simp [p8664] at ha; subst a; trivial
  · exact checked8664
theorem derived8664 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8664 := by
  apply localUnsat_implies_entails f8664 [c109, c104, c107, c110] c8664 unsat8664 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8665 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8665 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c14, some c45, some c6614, some c6557, some c8664, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8665 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8665 : lratChecker f8665 p8665 = .success := by decide +kernel
theorem unsat8665 : Unsatisfiable (PosFin 65) f8665 := by
  apply lratCheckerSound f8665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8665
  · intro a ha; simp [p8665] at ha; subst a; trivial
  · exact checked8665
theorem derived8665 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8665 := by
  apply localUnsat_implies_entails f8665 [c14, c45, c6614, c6557, c8664] c8665 unsat8665 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c6614 := h 6613 (by decide)
  have h3 : Entails.eval a c6557 := h 6556 (by decide)
  have h4 : Entails.eval a c8664 := derived8664 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8666 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, false), (⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8666 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c172, some c173, some c137, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8666 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8666 : lratChecker f8666 p8666 = .success := by decide +kernel
theorem unsat8666 : Unsatisfiable (PosFin 65) f8666 := by
  apply lratCheckerSound f8666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8666
  · intro a ha; simp [p8666] at ha; subst a; trivial
  · exact checked8666
theorem derived8666 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8666 := by
  apply localUnsat_implies_entails f8666 [c172, c173, c137] c8666 unsat8666 (by rfl) a
  have h0 : Entails.eval a c172 := h 171 (by decide)
  have h1 : Entails.eval a c173 := h 172 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8667 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨11, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8667 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8665, some c8269, some c8604, some c919, some c8666, some c908, some c905, some c937, some c928, some c8593, some c7770, some c296, some c6045, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8667 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8667 : lratChecker f8667 p8667 = .success := by decide +kernel
theorem unsat8667 : Unsatisfiable (PosFin 65) f8667 := by
  apply lratCheckerSound f8667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8667
  · intro a ha; simp [p8667] at ha; subst a; trivial
  · exact checked8667
theorem derived8667 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8667 := by
  apply localUnsat_implies_entails f8667 [c8665, c8269, c8604, c919, c8666, c908, c905, c937, c928, c8593, c7770, c296, c6045] c8667 unsat8667 (by rfl) a
  have h0 : Entails.eval a c8665 := derived8665 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8604 := derived8604 a h
  have h3 : Entails.eval a c919 := h 918 (by decide)
  have h4 : Entails.eval a c8666 := derived8666 a h
  have h5 : Entails.eval a c908 := h 907 (by decide)
  have h6 : Entails.eval a c905 := h 904 (by decide)
  have h7 : Entails.eval a c937 := h 936 (by decide)
  have h8 : Entails.eval a c928 := h 927 (by decide)
  have h9 : Entails.eval a c8593 := derived8593 a h
  have h10 : Entails.eval a c7770 := derived7770 a h
  have h11 : Entails.eval a c296 := h 295 (by decide)
  have h12 : Entails.eval a c6045 := h 6044 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8668 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨32, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8668 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4866, some c8604, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8668 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8668 : lratChecker f8668 p8668 = .success := by decide +kernel
theorem unsat8668 : Unsatisfiable (PosFin 65) f8668 := by
  apply lratCheckerSound f8668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8668
  · intro a ha; simp [p8668] at ha; subst a; trivial
  · exact checked8668
theorem derived8668 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8668 := by
  apply localUnsat_implies_entails f8668 [c4866, c8604] c8668 unsat8668 (by rfl) a
  have h0 : Entails.eval a c4866 := h 4865 (by decide)
  have h1 : Entails.eval a c8604 := derived8604 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8669 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨30, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8669 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8593, some c296, some c6039, some c6211, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8669 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8669 : lratChecker f8669 p8669 = .success := by decide +kernel
theorem unsat8669 : Unsatisfiable (PosFin 65) f8669 := by
  apply lratCheckerSound f8669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8669
  · intro a ha; simp [p8669] at ha; subst a; trivial
  · exact checked8669
theorem derived8669 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8669 := by
  apply localUnsat_implies_entails f8669 [c8593, c296, c6039, c6211] c8669 unsat8669 (by rfl) a
  have h0 : Entails.eval a c8593 := derived8593 a h
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c6039 := h 6038 (by decide)
  have h3 : Entails.eval a c6211 := h 6210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8670 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8670 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8646, some c8421, some c8653, some c8610, some c8665, some c8659, some c8668, some c919, some c8667, some c792, some c790, some c798, some c928, some c933, some c8669, some c8366, some c1100, some c1154, some c21, some c4586, some c474, some c6669, some c5283, some c5269, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8670 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked8670 : lratChecker f8670 p8670 = .success := by decide +kernel
theorem unsat8670 : Unsatisfiable (PosFin 65) f8670 := by
  apply lratCheckerSound f8670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8670
  · intro a ha; simp [p8670] at ha; subst a; trivial
  · exact checked8670
theorem derived8670 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8670 := by
  apply localUnsat_implies_entails f8670 [c8646, c8421, c8653, c8610, c8665, c8659, c8668, c919, c8667, c792, c790, c798, c928, c933, c8669, c8366, c1100, c1154, c21, c4586, c474, c6669, c5283, c5269] c8670 unsat8670 (by rfl) a
  have h0 : Entails.eval a c8646 := derived8646 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8653 := derived8653 a h
  have h3 : Entails.eval a c8610 := derived8610 a h
  have h4 : Entails.eval a c8665 := derived8665 a h
  have h5 : Entails.eval a c8659 := derived8659 a h
  have h6 : Entails.eval a c8668 := derived8668 a h
  have h7 : Entails.eval a c919 := h 918 (by decide)
  have h8 : Entails.eval a c8667 := derived8667 a h
  have h9 : Entails.eval a c792 := h 791 (by decide)
  have h10 : Entails.eval a c790 := h 789 (by decide)
  have h11 : Entails.eval a c798 := h 797 (by decide)
  have h12 : Entails.eval a c928 := h 927 (by decide)
  have h13 : Entails.eval a c933 := h 932 (by decide)
  have h14 : Entails.eval a c8669 := derived8669 a h
  have h15 : Entails.eval a c8366 := derived8366 a h
  have h16 : Entails.eval a c1100 := h 1099 (by decide)
  have h17 : Entails.eval a c1154 := h 1153 (by decide)
  have h18 : Entails.eval a c21 := h 20 (by decide)
  have h19 : Entails.eval a c4586 := h 4585 (by decide)
  have h20 : Entails.eval a c474 := h 473 (by decide)
  have h21 : Entails.eval a c6669 := h 6668 (by decide)
  have h22 : Entails.eval a c5283 := h 5282 (by decide)
  have h23 : Entails.eval a c5269 := h 5268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8671 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8671 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8653, some c8646, some c8610, some c8421, some c8661, some c8663, some c8665, some c8659, some c8662, some c8668, some c916, some c8670, some c924, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8671 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8671 : lratChecker f8671 p8671 = .success := by decide +kernel
theorem unsat8671 : Unsatisfiable (PosFin 65) f8671 := by
  apply lratCheckerSound f8671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8671
  · intro a ha; simp [p8671] at ha; subst a; trivial
  · exact checked8671
theorem derived8671 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8671 := by
  apply localUnsat_implies_entails f8671 [c8653, c8646, c8610, c8421, c8661, c8663, c8665, c8659, c8662, c8668, c916, c8670, c924] c8671 unsat8671 (by rfl) a
  have h0 : Entails.eval a c8653 := derived8653 a h
  have h1 : Entails.eval a c8646 := derived8646 a h
  have h2 : Entails.eval a c8610 := derived8610 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8661 := derived8661 a h
  have h5 : Entails.eval a c8663 := derived8663 a h
  have h6 : Entails.eval a c8665 := derived8665 a h
  have h7 : Entails.eval a c8659 := derived8659 a h
  have h8 : Entails.eval a c8662 := derived8662 a h
  have h9 : Entails.eval a c8668 := derived8668 a h
  have h10 : Entails.eval a c916 := h 915 (by decide)
  have h11 : Entails.eval a c8670 := derived8670 a h
  have h12 : Entails.eval a c924 := h 923 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8672 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8672 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5509, some c5515, some c5521, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8672 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8672 : lratChecker f8672 p8672 = .success := by decide +kernel
theorem unsat8672 : Unsatisfiable (PosFin 65) f8672 := by
  apply lratCheckerSound f8672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8672
  · intro a ha; simp [p8672] at ha; subst a; trivial
  · exact checked8672
theorem derived8672 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8672 := by
  apply localUnsat_implies_entails f8672 [c5509, c5515, c5521] c8672 unsat8672 (by rfl) a
  have h0 : Entails.eval a c5509 := h 5508 (by decide)
  have h1 : Entails.eval a c5515 := h 5514 (by decide)
  have h2 : Entails.eval a c5521 := h 5520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8673 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨18, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8673 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5700, some c5724, some c5608, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8673 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8673 : lratChecker f8673 p8673 = .success := by decide +kernel
theorem unsat8673 : Unsatisfiable (PosFin 65) f8673 := by
  apply lratCheckerSound f8673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8673
  · intro a ha; simp [p8673] at ha; subst a; trivial
  · exact checked8673
theorem derived8673 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8673 := by
  apply localUnsat_implies_entails f8673 [c5700, c5724, c5608] c8673 unsat8673 (by rfl) a
  have h0 : Entails.eval a c5700 := h 5699 (by decide)
  have h1 : Entails.eval a c5724 := h 5723 (by decide)
  have h2 : Entails.eval a c5608 := h 5607 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8674 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨18, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8674 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8608, some c4879, some c4878, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8674 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8674 : lratChecker f8674 p8674 = .success := by decide +kernel
theorem unsat8674 : Unsatisfiable (PosFin 65) f8674 := by
  apply lratCheckerSound f8674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8674
  · intro a ha; simp [p8674] at ha; subst a; trivial
  · exact checked8674
theorem derived8674 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8674 := by
  apply localUnsat_implies_entails f8674 [c8608, c4879, c4878] c8674 unsat8674 (by rfl) a
  have h0 : Entails.eval a c8608 := derived8608 a h
  have h1 : Entails.eval a c4879 := h 4878 (by decide)
  have h2 : Entails.eval a c4878 := h 4877 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8675 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨32, by decide⟩, true), (⟨11, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8675 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8672, some c4880, some c4879, some c4898, some c5615, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8675 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8675 : lratChecker f8675 p8675 = .success := by decide +kernel
theorem unsat8675 : Unsatisfiable (PosFin 65) f8675 := by
  apply lratCheckerSound f8675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8675
  · intro a ha; simp [p8675] at ha; subst a; trivial
  · exact checked8675
theorem derived8675 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8675 := by
  apply localUnsat_implies_entails f8675 [c8672, c4880, c4879, c4898, c5615] c8675 unsat8675 (by rfl) a
  have h0 : Entails.eval a c8672 := derived8672 a h
  have h1 : Entails.eval a c4880 := h 4879 (by decide)
  have h2 : Entails.eval a c4879 := h 4878 (by decide)
  have h3 : Entails.eval a c4898 := h 4897 (by decide)
  have h4 : Entails.eval a c5615 := h 5614 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8676 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8676 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c927, some c8544, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p8676 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8676 : lratChecker f8676 p8676 = .success := by decide +kernel
theorem unsat8676 : Unsatisfiable (PosFin 65) f8676 := by
  apply lratCheckerSound f8676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8676
  · intro a ha; simp [p8676] at ha; subst a; trivial
  · exact checked8676
theorem derived8676 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8676 := by
  apply localUnsat_implies_entails f8676 [c927, c8544] c8676 unsat8676 (by rfl) a
  have h0 : Entails.eval a c927 := h 926 (by decide)
  have h1 : Entails.eval a c8544 := derived8544 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8677 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8677 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8653, some c8646, some c8610, some c8421, some c8671, some c8672, some c8673, some c8659, some c8674, some c8675, some c8676, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8677 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8677 : lratChecker f8677 p8677 = .success := by decide +kernel
theorem unsat8677 : Unsatisfiable (PosFin 65) f8677 := by
  apply lratCheckerSound f8677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8677
  · intro a ha; simp [p8677] at ha; subst a; trivial
  · exact checked8677
theorem derived8677 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8677 := by
  apply localUnsat_implies_entails f8677 [c8653, c8646, c8610, c8421, c8671, c8672, c8673, c8659, c8674, c8675, c8676] c8677 unsat8677 (by rfl) a
  have h0 : Entails.eval a c8653 := derived8653 a h
  have h1 : Entails.eval a c8646 := derived8646 a h
  have h2 : Entails.eval a c8610 := derived8610 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8671 := derived8671 a h
  have h5 : Entails.eval a c8672 := derived8672 a h
  have h6 : Entails.eval a c8673 := derived8673 a h
  have h7 : Entails.eval a c8659 := derived8659 a h
  have h8 : Entails.eval a c8674 := derived8674 a h
  have h9 : Entails.eval a c8675 := derived8675 a h
  have h10 : Entails.eval a c8676 := derived8676 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8678 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8678 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c27, some c45, some c8366, some c6766, some c6557, some c6778, some c6643, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8678 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8678 : lratChecker f8678 p8678 = .success := by decide +kernel
theorem unsat8678 : Unsatisfiable (PosFin 65) f8678 := by
  apply lratCheckerSound f8678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8678
  · intro a ha; simp [p8678] at ha; subst a; trivial
  · exact checked8678
theorem derived8678 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8678 := by
  apply localUnsat_implies_entails f8678 [c27, c45, c8366, c6766, c6557, c6778, c6643] c8678 unsat8678 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c8366 := derived8366 a h
  have h3 : Entails.eval a c6766 := h 6765 (by decide)
  have h4 : Entails.eval a c6557 := h 6556 (by decide)
  have h5 : Entails.eval a c6778 := h 6777 (by decide)
  have h6 : Entails.eval a c6643 := h 6642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8679 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8679 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8366, some c36, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8679 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8679 : lratChecker f8679 p8679 = .success := by decide +kernel
theorem unsat8679 : Unsatisfiable (PosFin 65) f8679 := by
  apply lratCheckerSound f8679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8679
  · intro a ha; simp [p8679] at ha; subst a; trivial
  · exact checked8679
theorem derived8679 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8679 := by
  apply localUnsat_implies_entails f8679 [c8269, c8366, c36] c8679 unsat8679 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8366 := derived8366 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8680 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, false), (⟨64, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8680 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8590, some c8574, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8680 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8680 : lratChecker f8680 p8680 = .success := by decide +kernel
theorem unsat8680 : Unsatisfiable (PosFin 65) f8680 := by
  apply lratCheckerSound f8680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8680
  · intro a ha; simp [p8680] at ha; subst a; trivial
  · exact checked8680
theorem derived8680 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8680 := by
  apply localUnsat_implies_entails f8680 [c8590, c8574] c8680 unsat8680 (by rfl) a
  have h0 : Entails.eval a c8590 := derived8590 a h
  have h1 : Entails.eval a c8574 := derived8574 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8681 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8681 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8659, some c8679, some c8604, some c8680, some c8597, some c8528, some c8534, some c922, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8681 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8681 : lratChecker f8681 p8681 = .success := by decide +kernel
theorem unsat8681 : Unsatisfiable (PosFin 65) f8681 := by
  apply lratCheckerSound f8681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8681
  · intro a ha; simp [p8681] at ha; subst a; trivial
  · exact checked8681
theorem derived8681 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8681 := by
  apply localUnsat_implies_entails f8681 [c8659, c8679, c8604, c8680, c8597, c8528, c8534, c922] c8681 unsat8681 (by rfl) a
  have h0 : Entails.eval a c8659 := derived8659 a h
  have h1 : Entails.eval a c8679 := derived8679 a h
  have h2 : Entails.eval a c8604 := derived8604 a h
  have h3 : Entails.eval a c8680 := derived8680 a h
  have h4 : Entails.eval a c8597 := derived8597 a h
  have h5 : Entails.eval a c8528 := derived8528 a h
  have h6 : Entails.eval a c8534 := derived8534 a h
  have h7 : Entails.eval a c922 := h 921 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8682 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8682 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8646, some c8653, some c8677, some c8610, some c8678, some c8681, some c8659, some c8679, some c8604, some c8590, some c8670, some c916, some c934, some c5885, some c5886, some c790, some c5882, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8682 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8682 : lratChecker f8682 p8682 = .success := by decide +kernel
theorem unsat8682 : Unsatisfiable (PosFin 65) f8682 := by
  apply lratCheckerSound f8682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8682
  · intro a ha; simp [p8682] at ha; subst a; trivial
  · exact checked8682
theorem derived8682 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8682 := by
  apply localUnsat_implies_entails f8682 [c8421, c8646, c8653, c8677, c8610, c8678, c8681, c8659, c8679, c8604, c8590, c8670, c916, c934, c5885, c5886, c790, c5882] c8682 unsat8682 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8646 := derived8646 a h
  have h2 : Entails.eval a c8653 := derived8653 a h
  have h3 : Entails.eval a c8677 := derived8677 a h
  have h4 : Entails.eval a c8610 := derived8610 a h
  have h5 : Entails.eval a c8678 := derived8678 a h
  have h6 : Entails.eval a c8681 := derived8681 a h
  have h7 : Entails.eval a c8659 := derived8659 a h
  have h8 : Entails.eval a c8679 := derived8679 a h
  have h9 : Entails.eval a c8604 := derived8604 a h
  have h10 : Entails.eval a c8590 := derived8590 a h
  have h11 : Entails.eval a c8670 := derived8670 a h
  have h12 : Entails.eval a c916 := h 915 (by decide)
  have h13 : Entails.eval a c934 := h 933 (by decide)
  have h14 : Entails.eval a c5885 := h 5884 (by decide)
  have h15 : Entails.eval a c5886 := h 5885 (by decide)
  have h16 : Entails.eval a c790 := h 789 (by decide)
  have h17 : Entails.eval a c5882 := h 5881 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8683 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8683 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8646, some c8677, some c8679, some c8653, some c8610, some c8421, some c8678, some c8659, some c8604, some c8681, some c8682, some c8597, some c8609, some c920, some c933, some c928, some c907, some c131, some c134, some c2779, some c257, some c4219, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8683 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8683 : lratChecker f8683 p8683 = .success := by decide +kernel
theorem unsat8683 : Unsatisfiable (PosFin 65) f8683 := by
  apply lratCheckerSound f8683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8683
  · intro a ha; simp [p8683] at ha; subst a; trivial
  · exact checked8683
theorem derived8683 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8683 := by
  apply localUnsat_implies_entails f8683 [c8646, c8677, c8679, c8653, c8610, c8421, c8678, c8659, c8604, c8681, c8682, c8597, c8609, c920, c933, c928, c907, c131, c134, c2779, c257, c4219] c8683 unsat8683 (by rfl) a
  have h0 : Entails.eval a c8646 := derived8646 a h
  have h1 : Entails.eval a c8677 := derived8677 a h
  have h2 : Entails.eval a c8679 := derived8679 a h
  have h3 : Entails.eval a c8653 := derived8653 a h
  have h4 : Entails.eval a c8610 := derived8610 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8678 := derived8678 a h
  have h7 : Entails.eval a c8659 := derived8659 a h
  have h8 : Entails.eval a c8604 := derived8604 a h
  have h9 : Entails.eval a c8681 := derived8681 a h
  have h10 : Entails.eval a c8682 := derived8682 a h
  have h11 : Entails.eval a c8597 := derived8597 a h
  have h12 : Entails.eval a c8609 := derived8609 a h
  have h13 : Entails.eval a c920 := h 919 (by decide)
  have h14 : Entails.eval a c933 := h 932 (by decide)
  have h15 : Entails.eval a c928 := h 927 (by decide)
  have h16 : Entails.eval a c907 := h 906 (by decide)
  have h17 : Entails.eval a c131 := h 130 (by decide)
  have h18 : Entails.eval a c134 := h 133 (by decide)
  have h19 : Entails.eval a c2779 := h 2778 (by decide)
  have h20 : Entails.eval a c257 := h 256 (by decide)
  have h21 : Entails.eval a c4219 := h 4218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8684 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨53, by decide⟩, true), (⟨20, by decide⟩, true), (⟨64, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8684 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5591, some c5802, some c5761, some c5911, some c6160, some c6212, some c6229, some c8572, some c6064, some c5602, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p8684 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8684 : lratChecker f8684 p8684 = .success := by decide +kernel
theorem unsat8684 : Unsatisfiable (PosFin 65) f8684 := by
  apply lratCheckerSound f8684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8684
  · intro a ha; simp [p8684] at ha; subst a; trivial
  · exact checked8684
theorem derived8684 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8684 := by
  apply localUnsat_implies_entails f8684 [c5591, c5802, c5761, c5911, c6160, c6212, c6229, c8572, c6064, c5602] c8684 unsat8684 (by rfl) a
  have h0 : Entails.eval a c5591 := h 5590 (by decide)
  have h1 : Entails.eval a c5802 := h 5801 (by decide)
  have h2 : Entails.eval a c5761 := h 5760 (by decide)
  have h3 : Entails.eval a c5911 := h 5910 (by decide)
  have h4 : Entails.eval a c6160 := h 6159 (by decide)
  have h5 : Entails.eval a c6212 := h 6211 (by decide)
  have h6 : Entails.eval a c6229 := h 6228 (by decide)
  have h7 : Entails.eval a c8572 := derived8572 a h
  have h8 : Entails.eval a c6064 := h 6063 (by decide)
  have h9 : Entails.eval a c5602 := h 5601 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8685 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8685 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8679, some c27, some c8684, some c15, some c6593, some c6575, some c6557, some c7082, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8685 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8685 : lratChecker f8685 p8685 = .success := by decide +kernel
theorem unsat8685 : Unsatisfiable (PosFin 65) f8685 := by
  apply lratCheckerSound f8685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8685
  · intro a ha; simp [p8685] at ha; subst a; trivial
  · exact checked8685
theorem derived8685 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8685 := by
  apply localUnsat_implies_entails f8685 [c8679, c27, c8684, c15, c6593, c6575, c6557, c7082] c8685 unsat8685 (by rfl) a
  have h0 : Entails.eval a c8679 := derived8679 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c8684 := derived8684 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c6593 := h 6592 (by decide)
  have h5 : Entails.eval a c6575 := h 6574 (by decide)
  have h6 : Entails.eval a c6557 := h 6556 (by decide)
  have h7 : Entails.eval a c7082 := h 7081 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8686 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8686 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8610, some c8646, some c8653, some c8677, some c8679, some c8683, some c8685, some c8578, some c8659, some c8604, some c8608, some c8609, some c8572, some c920, some c933, some c913, some c912, some c5925, some c6022, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8686 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8686 : lratChecker f8686 p8686 = .success := by decide +kernel
theorem unsat8686 : Unsatisfiable (PosFin 65) f8686 := by
  apply lratCheckerSound f8686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8686
  · intro a ha; simp [p8686] at ha; subst a; trivial
  · exact checked8686
theorem derived8686 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8686 := by
  apply localUnsat_implies_entails f8686 [c8421, c8610, c8646, c8653, c8677, c8679, c8683, c8685, c8578, c8659, c8604, c8608, c8609, c8572, c920, c933, c913, c912, c5925, c6022] c8686 unsat8686 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8610 := derived8610 a h
  have h2 : Entails.eval a c8646 := derived8646 a h
  have h3 : Entails.eval a c8653 := derived8653 a h
  have h4 : Entails.eval a c8677 := derived8677 a h
  have h5 : Entails.eval a c8679 := derived8679 a h
  have h6 : Entails.eval a c8683 := derived8683 a h
  have h7 : Entails.eval a c8685 := derived8685 a h
  have h8 : Entails.eval a c8578 := derived8578 a h
  have h9 : Entails.eval a c8659 := derived8659 a h
  have h10 : Entails.eval a c8604 := derived8604 a h
  have h11 : Entails.eval a c8608 := derived8608 a h
  have h12 : Entails.eval a c8609 := derived8609 a h
  have h13 : Entails.eval a c8572 := derived8572 a h
  have h14 : Entails.eval a c920 := h 919 (by decide)
  have h15 : Entails.eval a c933 := h 932 (by decide)
  have h16 : Entails.eval a c913 := h 912 (by decide)
  have h17 : Entails.eval a c912 := h 911 (by decide)
  have h18 : Entails.eval a c5925 := h 5924 (by decide)
  have h19 : Entails.eval a c6022 := h 6021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8687 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8687 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c630, some c5997, some c5998, some c6002, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8687 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8687 : lratChecker f8687 p8687 = .success := by decide +kernel
theorem unsat8687 : Unsatisfiable (PosFin 65) f8687 := by
  apply lratCheckerSound f8687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8687
  · intro a ha; simp [p8687] at ha; subst a; trivial
  · exact checked8687
theorem derived8687 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8687 := by
  apply localUnsat_implies_entails f8687 [c630, c5997, c5998, c6002] c8687 unsat8687 (by rfl) a
  have h0 : Entails.eval a c630 := h 629 (by decide)
  have h1 : Entails.eval a c5997 := h 5996 (by decide)
  have h2 : Entails.eval a c5998 := h 5997 (by decide)
  have h3 : Entails.eval a c6002 := h 6001 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8688 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8688 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1406, some c1405, some c1195, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8688 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8688 : lratChecker f8688 p8688 = .success := by decide +kernel
theorem unsat8688 : Unsatisfiable (PosFin 65) f8688 := by
  apply lratCheckerSound f8688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8688
  · intro a ha; simp [p8688] at ha; subst a; trivial
  · exact checked8688
theorem derived8688 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8688 := by
  apply localUnsat_implies_entails f8688 [c1406, c1405, c1195] c8688 unsat8688 (by rfl) a
  have h0 : Entails.eval a c1406 := h 1405 (by decide)
  have h1 : Entails.eval a c1405 := h 1404 (by decide)
  have h2 : Entails.eval a c1195 := h 1194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8689 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8689 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4915, some c4902, some c4914, some c4907, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p8689 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8689 : lratChecker f8689 p8689 = .success := by decide +kernel
theorem unsat8689 : Unsatisfiable (PosFin 65) f8689 := by
  apply lratCheckerSound f8689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8689
  · intro a ha; simp [p8689] at ha; subst a; trivial
  · exact checked8689
theorem derived8689 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8689 := by
  apply localUnsat_implies_entails f8689 [c4915, c4902, c4914, c4907] c8689 unsat8689 (by rfl) a
  have h0 : Entails.eval a c4915 := h 4914 (by decide)
  have h1 : Entails.eval a c4902 := h 4901 (by decide)
  have h2 : Entails.eval a c4914 := h 4913 (by decide)
  have h3 : Entails.eval a c4907 := h 4906 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8690 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨64, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8690 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5675, some c5677, some c5671, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8690 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8690 : lratChecker f8690 p8690 = .success := by decide +kernel
theorem unsat8690 : Unsatisfiable (PosFin 65) f8690 := by
  apply lratCheckerSound f8690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8690
  · intro a ha; simp [p8690] at ha; subst a; trivial
  · exact checked8690
theorem derived8690 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8690 := by
  apply localUnsat_implies_entails f8690 [c5675, c5677, c5671] c8690 unsat8690 (by rfl) a
  have h0 : Entails.eval a c5675 := h 5674 (by decide)
  have h1 : Entails.eval a c5677 := h 5676 (by decide)
  have h2 : Entails.eval a c5671 := h 5670 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8691 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨30, by decide⟩, false), (⟨64, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8691 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6208, some c6232, some c5771, some c5772, some c5770, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8691 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8691 : lratChecker f8691 p8691 = .success := by decide +kernel
theorem unsat8691 : Unsatisfiable (PosFin 65) f8691 := by
  apply lratCheckerSound f8691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8691
  · intro a ha; simp [p8691] at ha; subst a; trivial
  · exact checked8691
theorem derived8691 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8691 := by
  apply localUnsat_implies_entails f8691 [c6208, c6232, c5771, c5772, c5770] c8691 unsat8691 (by rfl) a
  have h0 : Entails.eval a c6208 := h 6207 (by decide)
  have h1 : Entails.eval a c6232 := h 6231 (by decide)
  have h2 : Entails.eval a c5771 := h 5770 (by decide)
  have h3 : Entails.eval a c5772 := h 5771 (by decide)
  have h4 : Entails.eval a c5770 := h 5769 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8692 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8692 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c574, some c589, some c576, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8692 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8692 : lratChecker f8692 p8692 = .success := by decide +kernel
theorem unsat8692 : Unsatisfiable (PosFin 65) f8692 := by
  apply lratCheckerSound f8692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8692
  · intro a ha; simp [p8692] at ha; subst a; trivial
  · exact checked8692
theorem derived8692 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8692 := by
  apply localUnsat_implies_entails f8692 [c574, c589, c576] c8692 unsat8692 (by rfl) a
  have h0 : Entails.eval a c574 := h 573 (by decide)
  have h1 : Entails.eval a c589 := h 588 (by decide)
  have h2 : Entails.eval a c576 := h 575 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8693 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨53, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8693 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8687, some c8692, some c8269, some c8691, some c8690, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8693 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8693 : lratChecker f8693 p8693 = .success := by decide +kernel
theorem unsat8693 : Unsatisfiable (PosFin 65) f8693 := by
  apply lratCheckerSound f8693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8693
  · intro a ha; simp [p8693] at ha; subst a; trivial
  · exact checked8693
theorem derived8693 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8693 := by
  apply localUnsat_implies_entails f8693 [c8687, c8692, c8269, c8691, c8690] c8693 unsat8693 (by rfl) a
  have h0 : Entails.eval a c8687 := derived8687 a h
  have h1 : Entails.eval a c8692 := derived8692 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c8691 := derived8691 a h
  have h4 : Entails.eval a c8690 := derived8690 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8694 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8694 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5753, some c5790, some c5819, some c6104, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8694 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8694 : lratChecker f8694 p8694 = .success := by decide +kernel
theorem unsat8694 : Unsatisfiable (PosFin 65) f8694 := by
  apply lratCheckerSound f8694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8694
  · intro a ha; simp [p8694] at ha; subst a; trivial
  · exact checked8694
theorem derived8694 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8694 := by
  apply localUnsat_implies_entails f8694 [c5753, c5790, c5819, c6104] c8694 unsat8694 (by rfl) a
  have h0 : Entails.eval a c5753 := h 5752 (by decide)
  have h1 : Entails.eval a c5790 := h 5789 (by decide)
  have h2 : Entails.eval a c5819 := h 5818 (by decide)
  have h3 : Entails.eval a c6104 := h 6103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8695 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨53, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8695 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8694, some c569, some c578, some c565, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8695 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8695 : lratChecker f8695 p8695 = .success := by decide +kernel
theorem unsat8695 : Unsatisfiable (PosFin 65) f8695 := by
  apply lratCheckerSound f8695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8695
  · intro a ha; simp [p8695] at ha; subst a; trivial
  · exact checked8695
theorem derived8695 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8695 := by
  apply localUnsat_implies_entails f8695 [c8694, c569, c578, c565] c8695 unsat8695 (by rfl) a
  have h0 : Entails.eval a c8694 := derived8694 a h
  have h1 : Entails.eval a c569 := h 568 (by decide)
  have h2 : Entails.eval a c578 := h 577 (by decide)
  have h3 : Entails.eval a c565 := h 564 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8696 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨53, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8696 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8695, some c8687, some c8693, some c8692, some c8269, some c1267, some c1210, some c4457, some c8691, some c6117, some c221, some c220, some c214, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8696 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8696 : lratChecker f8696 p8696 = .success := by decide +kernel
theorem unsat8696 : Unsatisfiable (PosFin 65) f8696 := by
  apply lratCheckerSound f8696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8696
  · intro a ha; simp [p8696] at ha; subst a; trivial
  · exact checked8696
theorem derived8696 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8696 := by
  apply localUnsat_implies_entails f8696 [c8695, c8687, c8693, c8692, c8269, c1267, c1210, c4457, c8691, c6117, c221, c220, c214] c8696 unsat8696 (by rfl) a
  have h0 : Entails.eval a c8695 := derived8695 a h
  have h1 : Entails.eval a c8687 := derived8687 a h
  have h2 : Entails.eval a c8693 := derived8693 a h
  have h3 : Entails.eval a c8692 := derived8692 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c1267 := h 1266 (by decide)
  have h6 : Entails.eval a c1210 := h 1209 (by decide)
  have h7 : Entails.eval a c4457 := h 4456 (by decide)
  have h8 : Entails.eval a c8691 := derived8691 a h
  have h9 : Entails.eval a c6117 := h 6116 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c220 := h 219 (by decide)
  have h12 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8697 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨55, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8697 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5995, some c580, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8697 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8697 : lratChecker f8697 p8697 = .success := by decide +kernel
theorem unsat8697 : Unsatisfiable (PosFin 65) f8697 := by
  apply lratCheckerSound f8697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8697
  · intro a ha; simp [p8697] at ha; subst a; trivial
  · exact checked8697
theorem derived8697 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8697 := by
  apply localUnsat_implies_entails f8697 [c5995, c580] c8697 unsat8697 (by rfl) a
  have h0 : Entails.eval a c5995 := h 5994 (by decide)
  have h1 : Entails.eval a c580 := h 579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8698 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8698 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8695, some c8696, some c8697, some c8692, some c8269, some c5906, some c169, some c8691, some c6117, some c5776, some c5461, some c6105, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8698 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8698 : lratChecker f8698 p8698 = .success := by decide +kernel
theorem unsat8698 : Unsatisfiable (PosFin 65) f8698 := by
  apply lratCheckerSound f8698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8698
  · intro a ha; simp [p8698] at ha; subst a; trivial
  · exact checked8698
theorem derived8698 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8698 := by
  apply localUnsat_implies_entails f8698 [c8686, c8695, c8696, c8697, c8692, c8269, c5906, c169, c8691, c6117, c5776, c5461, c6105] c8698 unsat8698 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8695 := derived8695 a h
  have h2 : Entails.eval a c8696 := derived8696 a h
  have h3 : Entails.eval a c8697 := derived8697 a h
  have h4 : Entails.eval a c8692 := derived8692 a h
  have h5 : Entails.eval a c8269 := derived8269 a h
  have h6 : Entails.eval a c5906 := h 5905 (by decide)
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c8691 := derived8691 a h
  have h9 : Entails.eval a c6117 := h 6116 (by decide)
  have h10 : Entails.eval a c5776 := h 5775 (by decide)
  have h11 : Entails.eval a c5461 := h 5460 (by decide)
  have h12 : Entails.eval a c6105 := h 6104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8699 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8699 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1258, some c615, some c4724, some c5674, some c4454, some c1002, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8699 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8699 : lratChecker f8699 p8699 = .success := by decide +kernel
theorem unsat8699 : Unsatisfiable (PosFin 65) f8699 := by
  apply lratCheckerSound f8699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8699
  · intro a ha; simp [p8699] at ha; subst a; trivial
  · exact checked8699
theorem derived8699 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8699 := by
  apply localUnsat_implies_entails f8699 [c1258, c615, c4724, c5674, c4454, c1002] c8699 unsat8699 (by rfl) a
  have h0 : Entails.eval a c1258 := h 1257 (by decide)
  have h1 : Entails.eval a c615 := h 614 (by decide)
  have h2 : Entails.eval a c4724 := h 4723 (by decide)
  have h3 : Entails.eval a c5674 := h 5673 (by decide)
  have h4 : Entails.eval a c4454 := h 4453 (by decide)
  have h5 : Entails.eval a c1002 := h 1001 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8700 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨22, by decide⟩, true), (⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8700 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6207, some c6090, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8700 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8700 : lratChecker f8700 p8700 = .success := by decide +kernel
theorem unsat8700 : Unsatisfiable (PosFin 65) f8700 := by
  apply lratCheckerSound f8700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8700
  · intro a ha; simp [p8700] at ha; subst a; trivial
  · exact checked8700
theorem derived8700 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8700 := by
  apply localUnsat_implies_entails f8700 [c6207, c6090] c8700 unsat8700 (by rfl) a
  have h0 : Entails.eval a c6207 := h 6206 (by decide)
  have h1 : Entails.eval a c6090 := h 6089 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8701 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8701 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c614, some c628, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8701 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8701 : lratChecker f8701 p8701 = .success := by decide +kernel
theorem unsat8701 : Unsatisfiable (PosFin 65) f8701 := by
  apply lratCheckerSound f8701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8701
  · intro a ha; simp [p8701] at ha; subst a; trivial
  · exact checked8701
theorem derived8701 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8701 := by
  apply localUnsat_implies_entails f8701 [c614, c628] c8701 unsat8701 (by rfl) a
  have h0 : Entails.eval a c614 := h 613 (by decide)
  have h1 : Entails.eval a c628 := h 627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8702 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨11, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8702 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6207, some c6231, some c6171, some c1133, some c4435, some c4709, some c1004, some c6135, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8702 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8702 : lratChecker f8702 p8702 = .success := by decide +kernel
theorem unsat8702 : Unsatisfiable (PosFin 65) f8702 := by
  apply lratCheckerSound f8702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8702
  · intro a ha; simp [p8702] at ha; subst a; trivial
  · exact checked8702
theorem derived8702 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8702 := by
  apply localUnsat_implies_entails f8702 [c8269, c6207, c6231, c6171, c1133, c4435, c4709, c1004, c6135] c8702 unsat8702 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6207 := h 6206 (by decide)
  have h2 : Entails.eval a c6231 := h 6230 (by decide)
  have h3 : Entails.eval a c6171 := h 6170 (by decide)
  have h4 : Entails.eval a c1133 := h 1132 (by decide)
  have h5 : Entails.eval a c4435 := h 4434 (by decide)
  have h6 : Entails.eval a c4709 := h 4708 (by decide)
  have h7 : Entails.eval a c1004 := h 1003 (by decide)
  have h8 : Entails.eval a c6135 := h 6134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8703 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨11, by decide⟩, true), (⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8703 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8687, some c8692, some c8699, some c8702, some c614, some c622, some c609, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8703 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8703 : lratChecker f8703 p8703 = .success := by decide +kernel
theorem unsat8703 : Unsatisfiable (PosFin 65) f8703 := by
  apply lratCheckerSound f8703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8703
  · intro a ha; simp [p8703] at ha; subst a; trivial
  · exact checked8703
theorem derived8703 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8703 := by
  apply localUnsat_implies_entails f8703 [c8687, c8692, c8699, c8702, c614, c622, c609] c8703 unsat8703 (by rfl) a
  have h0 : Entails.eval a c8687 := derived8687 a h
  have h1 : Entails.eval a c8692 := derived8692 a h
  have h2 : Entails.eval a c8699 := derived8699 a h
  have h3 : Entails.eval a c8702 := derived8702 a h
  have h4 : Entails.eval a c614 := h 613 (by decide)
  have h5 : Entails.eval a c622 := h 621 (by decide)
  have h6 : Entails.eval a c609 := h 608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8704 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨55, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8704 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c1075, some c629, some c1130, some c4617, some c5978, some c4454, some c1011, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8704 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8704 : lratChecker f8704 p8704 = .success := by decide +kernel
theorem unsat8704 : Unsatisfiable (PosFin 65) f8704 := by
  apply lratCheckerSound f8704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8704
  · intro a ha; simp [p8704] at ha; subst a; trivial
  · exact checked8704
theorem derived8704 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8704 := by
  apply localUnsat_implies_entails f8704 [c8269, c1075, c629, c1130, c4617, c5978, c4454, c1011] c8704 unsat8704 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c1075 := h 1074 (by decide)
  have h2 : Entails.eval a c629 := h 628 (by decide)
  have h3 : Entails.eval a c1130 := h 1129 (by decide)
  have h4 : Entails.eval a c4617 := h 4616 (by decide)
  have h5 : Entails.eval a c5978 := h 5977 (by decide)
  have h6 : Entails.eval a c4454 := h 4453 (by decide)
  have h7 : Entails.eval a c1011 := h 1010 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8705 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨11, by decide⟩, true), (⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8705 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c371, some c1128, some c4874, some c3671, some c4705, some c4204, some c405, some c396, some c5809, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8705 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8705 : lratChecker f8705 p8705 = .success := by decide +kernel
theorem unsat8705 : Unsatisfiable (PosFin 65) f8705 := by
  apply lratCheckerSound f8705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8705
  · intro a ha; simp [p8705] at ha; subst a; trivial
  · exact checked8705
theorem derived8705 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8705 := by
  apply localUnsat_implies_entails f8705 [c371, c1128, c4874, c3671, c4705, c4204, c405, c396, c5809] c8705 unsat8705 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c1128 := h 1127 (by decide)
  have h2 : Entails.eval a c4874 := h 4873 (by decide)
  have h3 : Entails.eval a c3671 := h 3670 (by decide)
  have h4 : Entails.eval a c4705 := h 4704 (by decide)
  have h5 : Entails.eval a c4204 := h 4203 (by decide)
  have h6 : Entails.eval a c405 := h 404 (by decide)
  have h7 : Entails.eval a c396 := h 395 (by decide)
  have h8 : Entails.eval a c5809 := h 5808 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8706 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨55, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8706 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c579, some c8704, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8706 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8706 : lratChecker f8706 p8706 = .success := by decide +kernel
theorem unsat8706 : Unsatisfiable (PosFin 65) f8706 := by
  apply lratCheckerSound f8706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8706
  · intro a ha; simp [p8706] at ha; subst a; trivial
  · exact checked8706
theorem derived8706 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8706 := by
  apply localUnsat_implies_entails f8706 [c579, c8704] c8706 unsat8706 (by rfl) a
  have h0 : Entails.eval a c579 := h 578 (by decide)
  have h1 : Entails.eval a c8704 := derived8704 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8707 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8707 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6103, some c6242, some c6123, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8707 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8707 : lratChecker f8707 p8707 = .success := by decide +kernel
theorem unsat8707 : Unsatisfiable (PosFin 65) f8707 := by
  apply lratCheckerSound f8707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8707
  · intro a ha; simp [p8707] at ha; subst a; trivial
  · exact checked8707
theorem derived8707 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8707 := by
  apply localUnsat_implies_entails f8707 [c6103, c6242, c6123] c8707 unsat8707 (by rfl) a
  have h0 : Entails.eval a c6103 := h 6102 (by decide)
  have h1 : Entails.eval a c6242 := h 6241 (by decide)
  have h2 : Entails.eval a c6123 := h 6122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8708 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨51, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8708 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5665, some c5666, some c5668, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8708 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8708 : lratChecker f8708 p8708 = .success := by decide +kernel
theorem unsat8708 : Unsatisfiable (PosFin 65) f8708 := by
  apply lratCheckerSound f8708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8708
  · intro a ha; simp [p8708] at ha; subst a; trivial
  · exact checked8708
theorem derived8708 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8708 := by
  apply localUnsat_implies_entails f8708 [c5665, c5666, c5668] c8708 unsat8708 (by rfl) a
  have h0 : Entails.eval a c5665 := h 5664 (by decide)
  have h1 : Entails.eval a c5666 := h 5665 (by decide)
  have h2 : Entails.eval a c5668 := h 5667 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8709 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8709 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8698, some c8686, some c8421, some c8688, some c8703, some c8705, some c8706, some c8701, some c8708, some c578, some c8707, some c8699, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8709 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8709 : lratChecker f8709 p8709 = .success := by decide +kernel
theorem unsat8709 : Unsatisfiable (PosFin 65) f8709 := by
  apply lratCheckerSound f8709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8709
  · intro a ha; simp [p8709] at ha; subst a; trivial
  · exact checked8709
theorem derived8709 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8709 := by
  apply localUnsat_implies_entails f8709 [c8698, c8686, c8421, c8688, c8703, c8705, c8706, c8701, c8708, c578, c8707, c8699] c8709 unsat8709 (by rfl) a
  have h0 : Entails.eval a c8698 := derived8698 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8688 := derived8688 a h
  have h4 : Entails.eval a c8703 := derived8703 a h
  have h5 : Entails.eval a c8705 := derived8705 a h
  have h6 : Entails.eval a c8706 := derived8706 a h
  have h7 : Entails.eval a c8701 := derived8701 a h
  have h8 : Entails.eval a c8708 := derived8708 a h
  have h9 : Entails.eval a c578 := h 577 (by decide)
  have h10 : Entails.eval a c8707 := derived8707 a h
  have h11 : Entails.eval a c8699 := derived8699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8710 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8710 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1412, some c1195, some c1411, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8710 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8710 : lratChecker f8710 p8710 = .success := by decide +kernel
theorem unsat8710 : Unsatisfiable (PosFin 65) f8710 := by
  apply lratCheckerSound f8710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8710
  · intro a ha; simp [p8710] at ha; subst a; trivial
  · exact checked8710
theorem derived8710 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8710 := by
  apply localUnsat_implies_entails f8710 [c1412, c1195, c1411] c8710 unsat8710 (by rfl) a
  have h0 : Entails.eval a c1412 := h 1411 (by decide)
  have h1 : Entails.eval a c1195 := h 1194 (by decide)
  have h2 : Entails.eval a c1411 := h 1410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8711 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8711 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8698, some c8686, some c8421, some c8687, some c8710, some c8706, some c1128, some c1074, some c374, some c4598, some c4436, some c4324, some c405, some c4170, some c5809, some c396, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8711 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8711 : lratChecker f8711 p8711 = .success := by decide +kernel
theorem unsat8711 : Unsatisfiable (PosFin 65) f8711 := by
  apply lratCheckerSound f8711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8711
  · intro a ha; simp [p8711] at ha; subst a; trivial
  · exact checked8711
theorem derived8711 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8711 := by
  apply localUnsat_implies_entails f8711 [c8698, c8686, c8421, c8687, c8710, c8706, c1128, c1074, c374, c4598, c4436, c4324, c405, c4170, c5809, c396] c8711 unsat8711 (by rfl) a
  have h0 : Entails.eval a c8698 := derived8698 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8687 := derived8687 a h
  have h4 : Entails.eval a c8710 := derived8710 a h
  have h5 : Entails.eval a c8706 := derived8706 a h
  have h6 : Entails.eval a c1128 := h 1127 (by decide)
  have h7 : Entails.eval a c1074 := h 1073 (by decide)
  have h8 : Entails.eval a c374 := h 373 (by decide)
  have h9 : Entails.eval a c4598 := h 4597 (by decide)
  have h10 : Entails.eval a c4436 := h 4435 (by decide)
  have h11 : Entails.eval a c4324 := h 4323 (by decide)
  have h12 : Entails.eval a c405 := h 404 (by decide)
  have h13 : Entails.eval a c4170 := h 4169 (by decide)
  have h14 : Entails.eval a c5809 := h 5808 (by decide)
  have h15 : Entails.eval a c396 := h 395 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8712 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8712 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1192, some c1187, some c1410, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8712 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8712 : lratChecker f8712 p8712 = .success := by decide +kernel
theorem unsat8712 : Unsatisfiable (PosFin 65) f8712 := by
  apply lratCheckerSound f8712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8712
  · intro a ha; simp [p8712] at ha; subst a; trivial
  · exact checked8712
theorem derived8712 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8712 := by
  apply localUnsat_implies_entails f8712 [c1192, c1187, c1410] c8712 unsat8712 (by rfl) a
  have h0 : Entails.eval a c1192 := h 1191 (by decide)
  have h1 : Entails.eval a c1187 := h 1186 (by decide)
  have h2 : Entails.eval a c1410 := h 1409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8713 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8713 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6034, some c6127, some c6103, some c6057, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8713 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8713 : lratChecker f8713 p8713 = .success := by decide +kernel
theorem unsat8713 : Unsatisfiable (PosFin 65) f8713 := by
  apply lratCheckerSound f8713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8713
  · intro a ha; simp [p8713] at ha; subst a; trivial
  · exact checked8713
theorem derived8713 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8713 := by
  apply localUnsat_implies_entails f8713 [c6034, c6127, c6103, c6057] c8713 unsat8713 (by rfl) a
  have h0 : Entails.eval a c6034 := h 6033 (by decide)
  have h1 : Entails.eval a c6127 := h 6126 (by decide)
  have h2 : Entails.eval a c6103 := h 6102 (by decide)
  have h3 : Entails.eval a c6057 := h 6056 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8714 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8714 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6116, some c8713, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8714 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8714 : lratChecker f8714 p8714 = .success := by decide +kernel
theorem unsat8714 : Unsatisfiable (PosFin 65) f8714 := by
  apply lratCheckerSound f8714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8714
  · intro a ha; simp [p8714] at ha; subst a; trivial
  · exact checked8714
theorem derived8714 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8714 := by
  apply localUnsat_implies_entails f8714 [c6116, c8713] c8714 unsat8714 (by rfl) a
  have h0 : Entails.eval a c6116 := h 6115 (by decide)
  have h1 : Entails.eval a c8713 := derived8713 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8715 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8715 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c612, some c613, some c618, some c642, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8715 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8715 : lratChecker f8715 p8715 = .success := by decide +kernel
theorem unsat8715 : Unsatisfiable (PosFin 65) f8715 := by
  apply lratCheckerSound f8715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8715
  · intro a ha; simp [p8715] at ha; subst a; trivial
  · exact checked8715
theorem derived8715 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8715 := by
  apply localUnsat_implies_entails f8715 [c612, c613, c618, c642] c8715 unsat8715 (by rfl) a
  have h0 : Entails.eval a c612 := h 611 (by decide)
  have h1 : Entails.eval a c613 := h 612 (by decide)
  have h2 : Entails.eval a c618 := h 617 (by decide)
  have h3 : Entails.eval a c642 := h 641 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8716 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8716 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8692, some c8269, some c8712, some c8715, some c8702, some c6116, some c8713, some c5459, some c121, some c184, some c183, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8716 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8716 : lratChecker f8716 p8716 = .success := by decide +kernel
theorem unsat8716 : Unsatisfiable (PosFin 65) f8716 := by
  apply lratCheckerSound f8716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8716
  · intro a ha; simp [p8716] at ha; subst a; trivial
  · exact checked8716
theorem derived8716 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8716 := by
  apply localUnsat_implies_entails f8716 [c8686, c8692, c8269, c8712, c8715, c8702, c6116, c8713, c5459, c121, c184, c183] c8716 unsat8716 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8692 := derived8692 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c8712 := derived8712 a h
  have h4 : Entails.eval a c8715 := derived8715 a h
  have h5 : Entails.eval a c8702 := derived8702 a h
  have h6 : Entails.eval a c6116 := h 6115 (by decide)
  have h7 : Entails.eval a c8713 := derived8713 a h
  have h8 : Entails.eval a c5459 := h 5458 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8717 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8717 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8713, some c5754, some c6123, some c5394, some c6090, some c5898, some c5302, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8717 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8717 : lratChecker f8717 p8717 = .success := by decide +kernel
theorem unsat8717 : Unsatisfiable (PosFin 65) f8717 := by
  apply lratCheckerSound f8717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8717
  · intro a ha; simp [p8717] at ha; subst a; trivial
  · exact checked8717
theorem derived8717 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8717 := by
  apply localUnsat_implies_entails f8717 [c8713, c5754, c6123, c5394, c6090, c5898, c5302] c8717 unsat8717 (by rfl) a
  have h0 : Entails.eval a c8713 := derived8713 a h
  have h1 : Entails.eval a c5754 := h 5753 (by decide)
  have h2 : Entails.eval a c6123 := h 6122 (by decide)
  have h3 : Entails.eval a c5394 := h 5393 (by decide)
  have h4 : Entails.eval a c6090 := h 6089 (by decide)
  have h5 : Entails.eval a c5898 := h 5897 (by decide)
  have h6 : Entails.eval a c5302 := h 5301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8718 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8718 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8717, some c624, some c628, some c643, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8718 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8718 : lratChecker f8718 p8718 = .success := by decide +kernel
theorem unsat8718 : Unsatisfiable (PosFin 65) f8718 := by
  apply lratCheckerSound f8718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8718
  · intro a ha; simp [p8718] at ha; subst a; trivial
  · exact checked8718
theorem derived8718 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8718 := by
  apply localUnsat_implies_entails f8718 [c8717, c624, c628, c643] c8718 unsat8718 (by rfl) a
  have h0 : Entails.eval a c8717 := derived8717 a h
  have h1 : Entails.eval a c624 := h 623 (by decide)
  have h2 : Entails.eval a c628 := h 627 (by decide)
  have h3 : Entails.eval a c643 := h 642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8719 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨11, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨49, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8719 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1128, some c1074, some c374, some c4598, some c4436, some c4324, some c405, some c4170, some c5809, some c396, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8719 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8719 : lratChecker f8719 p8719 = .success := by decide +kernel
theorem unsat8719 : Unsatisfiable (PosFin 65) f8719 := by
  apply lratCheckerSound f8719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8719
  · intro a ha; simp [p8719] at ha; subst a; trivial
  · exact checked8719
theorem derived8719 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8719 := by
  apply localUnsat_implies_entails f8719 [c1128, c1074, c374, c4598, c4436, c4324, c405, c4170, c5809, c396] c8719 unsat8719 (by rfl) a
  have h0 : Entails.eval a c1128 := h 1127 (by decide)
  have h1 : Entails.eval a c1074 := h 1073 (by decide)
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c4598 := h 4597 (by decide)
  have h4 : Entails.eval a c4436 := h 4435 (by decide)
  have h5 : Entails.eval a c4324 := h 4323 (by decide)
  have h6 : Entails.eval a c405 := h 404 (by decide)
  have h7 : Entails.eval a c4170 := h 4169 (by decide)
  have h8 : Entails.eval a c5809 := h 5808 (by decide)
  have h9 : Entails.eval a c396 := h 395 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8720 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8720 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8698, some c8686, some c8421, some c8709, some c8711, some c8716, some c8710, some c8719, some c8718, some c578, some c565, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8720 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8720 : lratChecker f8720 p8720 = .success := by decide +kernel
theorem unsat8720 : Unsatisfiable (PosFin 65) f8720 := by
  apply lratCheckerSound f8720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8720
  · intro a ha; simp [p8720] at ha; subst a; trivial
  · exact checked8720
theorem derived8720 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8720 := by
  apply localUnsat_implies_entails f8720 [c8698, c8686, c8421, c8709, c8711, c8716, c8710, c8719, c8718, c578, c565] c8720 unsat8720 (by rfl) a
  have h0 : Entails.eval a c8698 := derived8698 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8709 := derived8709 a h
  have h4 : Entails.eval a c8711 := derived8711 a h
  have h5 : Entails.eval a c8716 := derived8716 a h
  have h6 : Entails.eval a c8710 := derived8710 a h
  have h7 : Entails.eval a c8719 := derived8719 a h
  have h8 : Entails.eval a c8718 := derived8718 a h
  have h9 : Entails.eval a c578 := h 577 (by decide)
  have h10 : Entails.eval a c565 := h 564 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8721 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8721 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6004, some c630, some c5999, some c5997, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8721 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8721 : lratChecker f8721 p8721 = .success := by decide +kernel
theorem unsat8721 : Unsatisfiable (PosFin 65) f8721 := by
  apply lratCheckerSound f8721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8721
  · intro a ha; simp [p8721] at ha; subst a; trivial
  · exact checked8721
theorem derived8721 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8721 := by
  apply localUnsat_implies_entails f8721 [c6004, c630, c5999, c5997] c8721 unsat8721 (by rfl) a
  have h0 : Entails.eval a c6004 := h 6003 (by decide)
  have h1 : Entails.eval a c630 := h 629 (by decide)
  have h2 : Entails.eval a c5999 := h 5998 (by decide)
  have h3 : Entails.eval a c5997 := h 5996 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8722 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8722 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8701, some c8713, some c8714, some c8700, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8722 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8722 : lratChecker f8722 p8722 = .success := by decide +kernel
theorem unsat8722 : Unsatisfiable (PosFin 65) f8722 := by
  apply lratCheckerSound f8722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8722
  · intro a ha; simp [p8722] at ha; subst a; trivial
  · exact checked8722
theorem derived8722 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8722 := by
  apply localUnsat_implies_entails f8722 [c8701, c8713, c8714, c8700] c8722 unsat8722 (by rfl) a
  have h0 : Entails.eval a c8701 := derived8701 a h
  have h1 : Entails.eval a c8713 := derived8713 a h
  have h2 : Entails.eval a c8714 := derived8714 a h
  have h3 : Entails.eval a c8700 := derived8700 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8723 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨55, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8723 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8722, some c5565, some c5564, some c5556, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8723 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8723 : lratChecker f8723 p8723 = .success := by decide +kernel
theorem unsat8723 : Unsatisfiable (PosFin 65) f8723 := by
  apply lratCheckerSound f8723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8723
  · intro a ha; simp [p8723] at ha; subst a; trivial
  · exact checked8723
theorem derived8723 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8723 := by
  apply localUnsat_implies_entails f8723 [c8722, c5565, c5564, c5556] c8723 unsat8723 (by rfl) a
  have h0 : Entails.eval a c8722 := derived8722 a h
  have h1 : Entails.eval a c5565 := h 5564 (by decide)
  have h2 : Entails.eval a c5564 := h 5563 (by decide)
  have h3 : Entails.eval a c5556 := h 5555 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8724 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8724 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8713, some c8714, some c8700, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8724 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8724 : lratChecker f8724 p8724 = .success := by decide +kernel
theorem unsat8724 : Unsatisfiable (PosFin 65) f8724 := by
  apply lratCheckerSound f8724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8724
  · intro a ha; simp [p8724] at ha; subst a; trivial
  · exact checked8724
theorem derived8724 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8724 := by
  apply localUnsat_implies_entails f8724 [c8713, c8714, c8700] c8724 unsat8724 (by rfl) a
  have h0 : Entails.eval a c8713 := derived8713 a h
  have h1 : Entails.eval a c8714 := derived8714 a h
  have h2 : Entails.eval a c8700 := derived8700 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8725 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8725 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8720, some c8698, some c8686, some c8721, some c8692, some c8723, some c8715, some c8666, some c8724, some c5459, some c5428, some c6171, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8725 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8725 : lratChecker f8725 p8725 = .success := by decide +kernel
theorem unsat8725 : Unsatisfiable (PosFin 65) f8725 := by
  apply lratCheckerSound f8725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8725
  · intro a ha; simp [p8725] at ha; subst a; trivial
  · exact checked8725
theorem derived8725 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8725 := by
  apply localUnsat_implies_entails f8725 [c8720, c8698, c8686, c8721, c8692, c8723, c8715, c8666, c8724, c5459, c5428, c6171] c8725 unsat8725 (by rfl) a
  have h0 : Entails.eval a c8720 := derived8720 a h
  have h1 : Entails.eval a c8698 := derived8698 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8721 := derived8721 a h
  have h4 : Entails.eval a c8692 := derived8692 a h
  have h5 : Entails.eval a c8723 := derived8723 a h
  have h6 : Entails.eval a c8715 := derived8715 a h
  have h7 : Entails.eval a c8666 := derived8666 a h
  have h8 : Entails.eval a c8724 := derived8724 a h
  have h9 : Entails.eval a c5459 := h 5458 (by decide)
  have h10 : Entails.eval a c5428 := h 5427 (by decide)
  have h11 : Entails.eval a c6171 := h 6170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8726 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨64, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8726 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c629, some c5986, some c5978, some c8480, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8726 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8726 : lratChecker f8726 p8726 = .success := by decide +kernel
theorem unsat8726 : Unsatisfiable (PosFin 65) f8726 := by
  apply lratCheckerSound f8726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8726
  · intro a ha; simp [p8726] at ha; subst a; trivial
  · exact checked8726
theorem derived8726 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8726 := by
  apply localUnsat_implies_entails f8726 [c629, c5986, c5978, c8480] c8726 unsat8726 (by rfl) a
  have h0 : Entails.eval a c629 := h 628 (by decide)
  have h1 : Entails.eval a c5986 := h 5985 (by decide)
  have h2 : Entails.eval a c5978 := h 5977 (by decide)
  have h3 : Entails.eval a c8480 := derived8480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8727 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8727 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5565, some c5564, some c5817, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p8727 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8727 : lratChecker f8727 p8727 = .success := by decide +kernel
theorem unsat8727 : Unsatisfiable (PosFin 65) f8727 := by
  apply lratCheckerSound f8727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8727
  · intro a ha; simp [p8727] at ha; subst a; trivial
  · exact checked8727
theorem derived8727 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8727 := by
  apply localUnsat_implies_entails f8727 [c5565, c5564, c5817] c8727 unsat8727 (by rfl) a
  have h0 : Entails.eval a c5565 := h 5564 (by decide)
  have h1 : Entails.eval a c5564 := h 5563 (by decide)
  have h2 : Entails.eval a c5817 := h 5816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8728 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8728 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8727, some c579, some c8726, some c8269, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8728 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8728 : lratChecker f8728 p8728 = .success := by decide +kernel
theorem unsat8728 : Unsatisfiable (PosFin 65) f8728 := by
  apply lratCheckerSound f8728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8728
  · intro a ha; simp [p8728] at ha; subst a; trivial
  · exact checked8728
theorem derived8728 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8728 := by
  apply localUnsat_implies_entails f8728 [c8727, c579, c8726, c8269] c8728 unsat8728 (by rfl) a
  have h0 : Entails.eval a c8727 := derived8727 a h
  have h1 : Entails.eval a c579 := h 578 (by decide)
  have h2 : Entails.eval a c8726 := derived8726 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8729 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨17, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8729 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c629, some c8713, some c5394, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8729 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8729 : lratChecker f8729 p8729 = .success := by decide +kernel
theorem unsat8729 : Unsatisfiable (PosFin 65) f8729 := by
  apply lratCheckerSound f8729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8729
  · intro a ha; simp [p8729] at ha; subst a; trivial
  · exact checked8729
theorem derived8729 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8729 := by
  apply localUnsat_implies_entails f8729 [c629, c8713, c5394] c8729 unsat8729 (by rfl) a
  have h0 : Entails.eval a c629 := h 628 (by decide)
  have h1 : Entails.eval a c8713 := derived8713 a h
  have h2 : Entails.eval a c5394 := h 5393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8730 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8730 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8698, some c8720, some c8725, some c8728, some c8686, some c8666, some c8729, some c5820, some c5829, some c5827, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8730 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8730 : lratChecker f8730 p8730 = .success := by decide +kernel
theorem unsat8730 : Unsatisfiable (PosFin 65) f8730 := by
  apply lratCheckerSound f8730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8730
  · intro a ha; simp [p8730] at ha; subst a; trivial
  · exact checked8730
theorem derived8730 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8730 := by
  apply localUnsat_implies_entails f8730 [c8698, c8720, c8725, c8728, c8686, c8666, c8729, c5820, c5829, c5827] c8730 unsat8730 (by rfl) a
  have h0 : Entails.eval a c8698 := derived8698 a h
  have h1 : Entails.eval a c8720 := derived8720 a h
  have h2 : Entails.eval a c8725 := derived8725 a h
  have h3 : Entails.eval a c8728 := derived8728 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8666 := derived8666 a h
  have h6 : Entails.eval a c8729 := derived8729 a h
  have h7 : Entails.eval a c5820 := h 5819 (by decide)
  have h8 : Entails.eval a c5829 := h 5828 (by decide)
  have h9 : Entails.eval a c5827 := h 5826 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8731 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8731 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c563, some c569, some c565, some c587, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p8731 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8731 : lratChecker f8731 p8731 = .success := by decide +kernel
theorem unsat8731 : Unsatisfiable (PosFin 65) f8731 := by
  apply lratCheckerSound f8731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8731
  · intro a ha; simp [p8731] at ha; subst a; trivial
  · exact checked8731
theorem derived8731 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8731 := by
  apply localUnsat_implies_entails f8731 [c563, c569, c565, c587] c8731 unsat8731 (by rfl) a
  have h0 : Entails.eval a c563 := h 562 (by decide)
  have h1 : Entails.eval a c569 := h 568 (by decide)
  have h2 : Entails.eval a c565 := h 564 (by decide)
  have h3 : Entails.eval a c587 := h 586 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8732 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8732 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5758, some c5755, some c5757, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p8732 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8732 : lratChecker f8732 p8732 = .success := by decide +kernel
theorem unsat8732 : Unsatisfiable (PosFin 65) f8732 := by
  apply lratCheckerSound f8732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8732
  · intro a ha; simp [p8732] at ha; subst a; trivial
  · exact checked8732
theorem derived8732 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8732 := by
  apply localUnsat_implies_entails f8732 [c5758, c5755, c5757] c8732 unsat8732 (by rfl) a
  have h0 : Entails.eval a c5758 := h 5757 (by decide)
  have h1 : Entails.eval a c5755 := h 5754 (by decide)
  have h2 : Entails.eval a c5757 := h 5756 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8733 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8733 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8727, some c8701, some c8713, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8733 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8733 : lratChecker f8733 p8733 = .success := by decide +kernel
theorem unsat8733 : Unsatisfiable (PosFin 65) f8733 := by
  apply lratCheckerSound f8733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8733
  · intro a ha; simp [p8733] at ha; subst a; trivial
  · exact checked8733
theorem derived8733 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8733 := by
  apply localUnsat_implies_entails f8733 [c8727, c8701, c8713] c8733 unsat8733 (by rfl) a
  have h0 : Entails.eval a c8727 := derived8727 a h
  have h1 : Entails.eval a c8701 := derived8701 a h
  have h2 : Entails.eval a c8713 := derived8713 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8734 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8734 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8698, some c8720, some c8725, some c8731, some c8730, some c8732, some c8733, some c8718, some c5820, some c5829, some c5827, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8734 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8734 : lratChecker f8734 p8734 = .success := by decide +kernel
theorem unsat8734 : Unsatisfiable (PosFin 65) f8734 := by
  apply lratCheckerSound f8734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8734
  · intro a ha; simp [p8734] at ha; subst a; trivial
  · exact checked8734
theorem derived8734 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8734 := by
  apply localUnsat_implies_entails f8734 [c8686, c8698, c8720, c8725, c8731, c8730, c8732, c8733, c8718, c5820, c5829, c5827] c8734 unsat8734 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8698 := derived8698 a h
  have h2 : Entails.eval a c8720 := derived8720 a h
  have h3 : Entails.eval a c8725 := derived8725 a h
  have h4 : Entails.eval a c8731 := derived8731 a h
  have h5 : Entails.eval a c8730 := derived8730 a h
  have h6 : Entails.eval a c8732 := derived8732 a h
  have h7 : Entails.eval a c8733 := derived8733 a h
  have h8 : Entails.eval a c8718 := derived8718 a h
  have h9 : Entails.eval a c5820 := h 5819 (by decide)
  have h10 : Entails.eval a c5829 := h 5828 (by decide)
  have h11 : Entails.eval a c5827 := h 5826 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8735 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8735 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c144, some c8690, some c5429, some c6172, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8735 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8735 : lratChecker f8735 p8735 = .success := by decide +kernel
theorem unsat8735 : Unsatisfiable (PosFin 65) f8735 := by
  apply lratCheckerSound f8735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8735
  · intro a ha; simp [p8735] at ha; subst a; trivial
  · exact checked8735
theorem derived8735 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8735 := by
  apply localUnsat_implies_entails f8735 [c8269, c144, c8690, c5429, c6172] c8735 unsat8735 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c8690 := derived8690 a h
  have h3 : Entails.eval a c5429 := h 5428 (by decide)
  have h4 : Entails.eval a c6172 := h 6171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8736 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8736 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6116, some c8700, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8736 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8736 : lratChecker f8736 p8736 = .success := by decide +kernel
theorem unsat8736 : Unsatisfiable (PosFin 65) f8736 := by
  apply lratCheckerSound f8736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8736
  · intro a ha; simp [p8736] at ha; subst a; trivial
  · exact checked8736
theorem derived8736 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8736 := by
  apply localUnsat_implies_entails f8736 [c6116, c8700] c8736 unsat8736 (by rfl) a
  have h0 : Entails.eval a c6116 := h 6115 (by decide)
  have h1 : Entails.eval a c8700 := derived8700 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8737 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8737 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8708, some c8736, some c6084, some c6099, some c6150, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8737 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8737 : lratChecker f8737 p8737 = .success := by decide +kernel
theorem unsat8737 : Unsatisfiable (PosFin 65) f8737 := by
  apply lratCheckerSound f8737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8737
  · intro a ha; simp [p8737] at ha; subst a; trivial
  · exact checked8737
theorem derived8737 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8737 := by
  apply localUnsat_implies_entails f8737 [c8708, c8736, c6084, c6099, c6150] c8737 unsat8737 (by rfl) a
  have h0 : Entails.eval a c8708 := derived8708 a h
  have h1 : Entails.eval a c8736 := derived8736 a h
  have h2 : Entails.eval a c6084 := h 6083 (by decide)
  have h3 : Entails.eval a c6099 := h 6098 (by decide)
  have h4 : Entails.eval a c6150 := h 6149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8738 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8738 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8722, some c8735, some c8737, some c623, some c609, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8738 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8738 : lratChecker f8738 p8738 = .success := by decide +kernel
theorem unsat8738 : Unsatisfiable (PosFin 65) f8738 := by
  apply lratCheckerSound f8738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8738
  · intro a ha; simp [p8738] at ha; subst a; trivial
  · exact checked8738
theorem derived8738 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8738 := by
  apply localUnsat_implies_entails f8738 [c8722, c8735, c8737, c623, c609] c8738 unsat8738 (by rfl) a
  have h0 : Entails.eval a c8722 := derived8722 a h
  have h1 : Entails.eval a c8735 := derived8735 a h
  have h2 : Entails.eval a c8737 := derived8737 a h
  have h3 : Entails.eval a c623 := h 622 (by decide)
  have h4 : Entails.eval a c609 := h 608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8739 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨22, by decide⟩, false), (⟨29, by decide⟩, true), (⟨50, by decide⟩, true), (⟨19, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8739 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c144, some c1267, some c1210, some c5429, some c4457, some c4725, some c346, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8739 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8739 : lratChecker f8739 p8739 = .success := by decide +kernel
theorem unsat8739 : Unsatisfiable (PosFin 65) f8739 := by
  apply lratCheckerSound f8739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8739
  · intro a ha; simp [p8739] at ha; subst a; trivial
  · exact checked8739
theorem derived8739 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8739 := by
  apply localUnsat_implies_entails f8739 [c144, c1267, c1210, c5429, c4457, c4725, c346] c8739 unsat8739 (by rfl) a
  have h0 : Entails.eval a c144 := h 143 (by decide)
  have h1 : Entails.eval a c1267 := h 1266 (by decide)
  have h2 : Entails.eval a c1210 := h 1209 (by decide)
  have h3 : Entails.eval a c5429 := h 5428 (by decide)
  have h4 : Entails.eval a c4457 := h 4456 (by decide)
  have h5 : Entails.eval a c4725 := h 4724 (by decide)
  have h6 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8740 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨18, by decide⟩, false), (⟨50, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8740 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c122, some c186, some c145, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8740 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8740 : lratChecker f8740 p8740 = .success := by decide +kernel
theorem unsat8740 : Unsatisfiable (PosFin 65) f8740 := by
  apply lratCheckerSound f8740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8740
  · intro a ha; simp [p8740] at ha; subst a; trivial
  · exact checked8740
theorem derived8740 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8740 := by
  apply localUnsat_implies_entails f8740 [c8686, c122, c186, c145] c8740 unsat8740 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8741 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8741 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8734, some c8686, some c8687, some c8692, some c8738, some c8715, some c8724, some c8736, some c8739, some c8740, some c5459, some c5428, some c6171, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8741 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8741 : lratChecker f8741 p8741 = .success := by decide +kernel
theorem unsat8741 : Unsatisfiable (PosFin 65) f8741 := by
  apply lratCheckerSound f8741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8741
  · intro a ha; simp [p8741] at ha; subst a; trivial
  · exact checked8741
theorem derived8741 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8741 := by
  apply localUnsat_implies_entails f8741 [c8734, c8686, c8687, c8692, c8738, c8715, c8724, c8736, c8739, c8740, c5459, c5428, c6171] c8741 unsat8741 (by rfl) a
  have h0 : Entails.eval a c8734 := derived8734 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8687 := derived8687 a h
  have h3 : Entails.eval a c8692 := derived8692 a h
  have h4 : Entails.eval a c8738 := derived8738 a h
  have h5 : Entails.eval a c8715 := derived8715 a h
  have h6 : Entails.eval a c8724 := derived8724 a h
  have h7 : Entails.eval a c8736 := derived8736 a h
  have h8 : Entails.eval a c8739 := derived8739 a h
  have h9 : Entails.eval a c8740 := derived8740 a h
  have h10 : Entails.eval a c5459 := h 5458 (by decide)
  have h11 : Entails.eval a c5428 := h 5427 (by decide)
  have h12 : Entails.eval a c6171 := h 6170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8742 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨27, by decide⟩, false), (⟨55, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8742 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c629, some c8706, some c5978, some c5980, some c1210, some c283, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8742 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8742 : lratChecker f8742 p8742 = .success := by decide +kernel
theorem unsat8742 : Unsatisfiable (PosFin 65) f8742 := by
  apply lratCheckerSound f8742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8742
  · intro a ha; simp [p8742] at ha; subst a; trivial
  · exact checked8742
theorem derived8742 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8742 := by
  apply localUnsat_implies_entails f8742 [c8269, c629, c8706, c5978, c5980, c1210, c283] c8742 unsat8742 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c629 := h 628 (by decide)
  have h2 : Entails.eval a c8706 := derived8706 a h
  have h3 : Entails.eval a c5978 := h 5977 (by decide)
  have h4 : Entails.eval a c5980 := h 5979 (by decide)
  have h5 : Entails.eval a c1210 := h 1209 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8743 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8743 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c144, some c5475, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8743 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8743 : lratChecker f8743 p8743 = .success := by decide +kernel
theorem unsat8743 : Unsatisfiable (PosFin 65) f8743 := by
  apply lratCheckerSound f8743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8743
  · intro a ha; simp [p8743] at ha; subst a; trivial
  · exact checked8743
theorem derived8743 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8743 := by
  apply localUnsat_implies_entails f8743 [c144, c5475] c8743 unsat8743 (by rfl) a
  have h0 : Entails.eval a c144 := h 143 (by decide)
  have h1 : Entails.eval a c5475 := h 5474 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8744 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8744 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5474, some c145, some c5308, some c180, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8744 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8744 : lratChecker f8744 p8744 = .success := by decide +kernel
theorem unsat8744 : Unsatisfiable (PosFin 65) f8744 := by
  apply lratCheckerSound f8744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8744
  · intro a ha; simp [p8744] at ha; subst a; trivial
  · exact checked8744
theorem derived8744 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8744 := by
  apply localUnsat_implies_entails f8744 [c5474, c145, c5308, c180] c8744 unsat8744 (by rfl) a
  have h0 : Entails.eval a c5474 := h 5473 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c5308 := h 5307 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8745 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨51, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨20, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8745 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c852, some c847, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8745 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8745 : lratChecker f8745 p8745 = .success := by decide +kernel
theorem unsat8745 : Unsatisfiable (PosFin 65) f8745 := by
  apply lratCheckerSound f8745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8745
  · intro a ha; simp [p8745] at ha; subst a; trivial
  · exact checked8745
theorem derived8745 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8745 := by
  apply localUnsat_implies_entails f8745 [c852, c847] c8745 unsat8745 (by rfl) a
  have h0 : Entails.eval a c852 := h 851 (by decide)
  have h1 : Entails.eval a c847 := h 846 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8746 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8746 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c145, some c175, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8746 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8746 : lratChecker f8746 p8746 = .success := by decide +kernel
theorem unsat8746 : Unsatisfiable (PosFin 65) f8746 := by
  apply lratCheckerSound f8746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8746
  · intro a ha; simp [p8746] at ha; subst a; trivial
  · exact checked8746
theorem derived8746 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8746 := by
  apply localUnsat_implies_entails f8746 [c145, c175] c8746 unsat8746 (by rfl) a
  have h0 : Entails.eval a c145 := h 144 (by decide)
  have h1 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8747 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨27, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8747 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8741, some c8734, some c8686, some c8742, some c8743, some c8744, some c8746, some c5476, some c5485, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8747 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8747 : lratChecker f8747 p8747 = .success := by decide +kernel
theorem unsat8747 : Unsatisfiable (PosFin 65) f8747 := by
  apply lratCheckerSound f8747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8747
  · intro a ha; simp [p8747] at ha; subst a; trivial
  · exact checked8747
theorem derived8747 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8747 := by
  apply localUnsat_implies_entails f8747 [c8741, c8734, c8686, c8742, c8743, c8744, c8746, c5476, c5485] c8747 unsat8747 (by rfl) a
  have h0 : Entails.eval a c8741 := derived8741 a h
  have h1 : Entails.eval a c8734 := derived8734 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8742 := derived8742 a h
  have h4 : Entails.eval a c8743 := derived8743 a h
  have h5 : Entails.eval a c8744 := derived8744 a h
  have h6 : Entails.eval a c8746 := derived8746 a h
  have h7 : Entails.eval a c5476 := h 5475 (by decide)
  have h8 : Entails.eval a c5485 := h 5484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8748 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨30, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8748 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c573, some c617, some c1183, some c1256, some c4433, some c5684, some c731, some c737, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8748 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8748 : lratChecker f8748 p8748 = .success := by decide +kernel
theorem unsat8748 : Unsatisfiable (PosFin 65) f8748 := by
  apply lratCheckerSound f8748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8748
  · intro a ha; simp [p8748] at ha; subst a; trivial
  · exact checked8748
theorem derived8748 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8748 := by
  apply localUnsat_implies_entails f8748 [c573, c617, c1183, c1256, c4433, c5684, c731, c737] c8748 unsat8748 (by rfl) a
  have h0 : Entails.eval a c573 := h 572 (by decide)
  have h1 : Entails.eval a c617 := h 616 (by decide)
  have h2 : Entails.eval a c1183 := h 1182 (by decide)
  have h3 : Entails.eval a c1256 := h 1255 (by decide)
  have h4 : Entails.eval a c4433 := h 4432 (by decide)
  have h5 : Entails.eval a c5684 := h 5683 (by decide)
  have h6 : Entails.eval a c731 := h 730 (by decide)
  have h7 : Entails.eval a c737 := h 736 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8749 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨53, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8749 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5435, some c5463, some c5388, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8749 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8749 : lratChecker f8749 p8749 = .success := by decide +kernel
theorem unsat8749 : Unsatisfiable (PosFin 65) f8749 := by
  apply lratCheckerSound f8749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8749
  · intro a ha; simp [p8749] at ha; subst a; trivial
  · exact checked8749
theorem derived8749 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8749 := by
  apply localUnsat_implies_entails f8749 [c5435, c5463, c5388] c8749 unsat8749 (by rfl) a
  have h0 : Entails.eval a c5435 := h 5434 (by decide)
  have h1 : Entails.eval a c5463 := h 5462 (by decide)
  have h2 : Entails.eval a c5388 := h 5387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8750 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨17, by decide⟩, false), (⟨53, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨50, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8750 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c128, some c122, some c148, some c5300, some c5451, some c5453, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8750 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8750 : lratChecker f8750 p8750 = .success := by decide +kernel
theorem unsat8750 : Unsatisfiable (PosFin 65) f8750 := by
  apply lratCheckerSound f8750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8750
  · intro a ha; simp [p8750] at ha; subst a; trivial
  · exact checked8750
theorem derived8750 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8750 := by
  apply localUnsat_implies_entails f8750 [c128, c122, c148, c5300, c5451, c5453] c8750 unsat8750 (by rfl) a
  have h0 : Entails.eval a c128 := h 127 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c5300 := h 5299 (by decide)
  have h4 : Entails.eval a c5451 := h 5450 (by decide)
  have h5 : Entails.eval a c5453 := h 5452 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8750

end CochromaticTwenty.Certificates.FixedCore0
