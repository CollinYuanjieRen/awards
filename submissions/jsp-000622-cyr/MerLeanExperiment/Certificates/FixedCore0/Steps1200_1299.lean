import MerLeanExperiment.Certificates.FixedCore0.Steps1100_1199

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8751 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨25, by decide⟩, false), (⟨23, by decide⟩, true), (⟨30, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨27, by decide⟩, false), (⟨55, by decide⟩, false), (⟨19, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8751 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8749, some c129, some c8750, some c5457, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8751 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8751 : lratChecker f8751 p8751 = .success := by decide +kernel
theorem unsat8751 : Unsatisfiable (PosFin 65) f8751 := by
  apply lratCheckerSound f8751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8751
  · intro a ha; simp [p8751] at ha; subst a; trivial
  · exact checked8751
theorem derived8751 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8751 := by
  apply localUnsat_implies_entails f8751 [c8749, c129, c8750, c5457] c8751 unsat8751 (by rfl) a
  have h0 : Entails.eval a c8749 := derived8749 a h
  have h1 : Entails.eval a c129 := h 128 (by decide)
  have h2 : Entails.eval a c8750 := derived8750 a h
  have h3 : Entails.eval a c5457 := h 5456 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8752 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨51, by decide⟩, true), (⟨29, by decide⟩, true), (⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8752 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5362, some c5489, some c5490, some c5366, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p8752 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8752 : lratChecker f8752 p8752 = .success := by decide +kernel
theorem unsat8752 : Unsatisfiable (PosFin 65) f8752 := by
  apply lratCheckerSound f8752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8752
  · intro a ha; simp [p8752] at ha; subst a; trivial
  · exact checked8752
theorem derived8752 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8752 := by
  apply localUnsat_implies_entails f8752 [c5362, c5489, c5490, c5366] c8752 unsat8752 (by rfl) a
  have h0 : Entails.eval a c5362 := h 5361 (by decide)
  have h1 : Entails.eval a c5489 := h 5488 (by decide)
  have h2 : Entails.eval a c5490 := h 5489 (by decide)
  have h3 : Entails.eval a c5366 := h 5365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8753 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8753 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8752, some c121, some c122, some c5320, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8753 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8753 : lratChecker f8753 p8753 = .success := by decide +kernel
theorem unsat8753 : Unsatisfiable (PosFin 65) f8753 := by
  apply lratCheckerSound f8753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8753
  · intro a ha; simp [p8753] at ha; subst a; trivial
  · exact checked8753
theorem derived8753 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8753 := by
  apply localUnsat_implies_entails f8753 [c8752, c121, c122, c5320] c8753 unsat8753 (by rfl) a
  have h0 : Entails.eval a c8752 := derived8752 a h
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c5320 := h 5319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8754 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8754 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5485, some c5386, some c5418, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8754 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8754 : lratChecker f8754 p8754 = .success := by decide +kernel
theorem unsat8754 : Unsatisfiable (PosFin 65) f8754 := by
  apply lratCheckerSound f8754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8754
  · intro a ha; simp [p8754] at ha; subst a; trivial
  · exact checked8754
theorem derived8754 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8754 := by
  apply localUnsat_implies_entails f8754 [c5485, c5386, c5418] c8754 unsat8754 (by rfl) a
  have h0 : Entails.eval a c5485 := h 5484 (by decide)
  have h1 : Entails.eval a c5386 := h 5385 (by decide)
  have h2 : Entails.eval a c5418 := h 5417 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8755 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8755 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8741, some c8734, some c8686, some c8747, some c566, some c561, some c579, some c585, some c583, some c567, some c573, some c590, some c586, some c8748, some c8751, some c8753, some c611, some c8754, some c175, some c5457, some c5446, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8755 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8755 : lratChecker f8755 p8755 = .success := by decide +kernel
theorem unsat8755 : Unsatisfiable (PosFin 65) f8755 := by
  apply lratCheckerSound f8755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8755
  · intro a ha; simp [p8755] at ha; subst a; trivial
  · exact checked8755
theorem derived8755 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8755 := by
  apply localUnsat_implies_entails f8755 [c8741, c8734, c8686, c8747, c566, c561, c579, c585, c583, c567, c573, c590, c586, c8748, c8751, c8753, c611, c8754, c175, c5457, c5446] c8755 unsat8755 (by rfl) a
  have h0 : Entails.eval a c8741 := derived8741 a h
  have h1 : Entails.eval a c8734 := derived8734 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8747 := derived8747 a h
  have h4 : Entails.eval a c566 := h 565 (by decide)
  have h5 : Entails.eval a c561 := h 560 (by decide)
  have h6 : Entails.eval a c579 := h 578 (by decide)
  have h7 : Entails.eval a c585 := h 584 (by decide)
  have h8 : Entails.eval a c583 := h 582 (by decide)
  have h9 : Entails.eval a c567 := h 566 (by decide)
  have h10 : Entails.eval a c573 := h 572 (by decide)
  have h11 : Entails.eval a c590 := h 589 (by decide)
  have h12 : Entails.eval a c586 := h 585 (by decide)
  have h13 : Entails.eval a c8748 := derived8748 a h
  have h14 : Entails.eval a c8751 := derived8751 a h
  have h15 : Entails.eval a c8753 := derived8753 a h
  have h16 : Entails.eval a c611 := h 610 (by decide)
  have h17 : Entails.eval a c8754 := derived8754 a h
  have h18 : Entails.eval a c175 := h 174 (by decide)
  have h19 : Entails.eval a c5457 := h 5456 (by decide)
  have h20 : Entails.eval a c5446 := h 5445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8756 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8756 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c144, some c1267, some c1210, some c5396, some c4725, some c8713, some c639, some c632, some c6104, some c864, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8756 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8756 : lratChecker f8756 p8756 = .success := by decide +kernel
theorem unsat8756 : Unsatisfiable (PosFin 65) f8756 := by
  apply lratCheckerSound f8756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8756
  · intro a ha; simp [p8756] at ha; subst a; trivial
  · exact checked8756
theorem derived8756 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8756 := by
  apply localUnsat_implies_entails f8756 [c144, c1267, c1210, c5396, c4725, c8713, c639, c632, c6104, c864] c8756 unsat8756 (by rfl) a
  have h0 : Entails.eval a c144 := h 143 (by decide)
  have h1 : Entails.eval a c1267 := h 1266 (by decide)
  have h2 : Entails.eval a c1210 := h 1209 (by decide)
  have h3 : Entails.eval a c5396 := h 5395 (by decide)
  have h4 : Entails.eval a c4725 := h 4724 (by decide)
  have h5 : Entails.eval a c8713 := derived8713 a h
  have h6 : Entails.eval a c639 := h 638 (by decide)
  have h7 : Entails.eval a c632 := h 631 (by decide)
  have h8 : Entails.eval a c6104 := h 6103 (by decide)
  have h9 : Entails.eval a c864 := h 863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8757 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8757 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8713, some c5394, some c6123, some c145, some c179, some c5311, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8757 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8757 : lratChecker f8757 p8757 = .success := by decide +kernel
theorem unsat8757 : Unsatisfiable (PosFin 65) f8757 := by
  apply lratCheckerSound f8757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8757
  · intro a ha; simp [p8757] at ha; subst a; trivial
  · exact checked8757
theorem derived8757 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8757 := by
  apply localUnsat_implies_entails f8757 [c8713, c5394, c6123, c145, c179, c5311] c8757 unsat8757 (by rfl) a
  have h0 : Entails.eval a c8713 := derived8713 a h
  have h1 : Entails.eval a c5394 := h 5393 (by decide)
  have h2 : Entails.eval a c6123 := h 6122 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c179 := h 178 (by decide)
  have h5 : Entails.eval a c5311 := h 5310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8758 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8758 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8756, some c8757, some c624, some c628, some c643, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8758 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8758 : lratChecker f8758 p8758 = .success := by decide +kernel
theorem unsat8758 : Unsatisfiable (PosFin 65) f8758 := by
  apply lratCheckerSound f8758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8758
  · intro a ha; simp [p8758] at ha; subst a; trivial
  · exact checked8758
theorem derived8758 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8758 := by
  apply localUnsat_implies_entails f8758 [c8756, c8757, c624, c628, c643] c8758 unsat8758 (by rfl) a
  have h0 : Entails.eval a c8756 := derived8756 a h
  have h1 : Entails.eval a c8757 := derived8757 a h
  have h2 : Entails.eval a c624 := h 623 (by decide)
  have h3 : Entails.eval a c628 := h 627 (by decide)
  have h4 : Entails.eval a c643 := h 642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8759 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8759 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8743, some c5474, some c145, some c179, some c186, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8759 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8759 : lratChecker f8759 p8759 = .success := by decide +kernel
theorem unsat8759 : Unsatisfiable (PosFin 65) f8759 := by
  apply lratCheckerSound f8759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8759
  · intro a ha; simp [p8759] at ha; subst a; trivial
  · exact checked8759
theorem derived8759 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8759 := by
  apply localUnsat_implies_entails f8759 [c8743, c5474, c145, c179, c186] c8759 unsat8759 (by rfl) a
  have h0 : Entails.eval a c8743 := derived8743 a h
  have h1 : Entails.eval a c5474 := h 5473 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8760 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8760 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8758, some c8743, some c8759, some c8746, some c5485, some c5476, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8760 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8760 : lratChecker f8760 p8760 = .success := by decide +kernel
theorem unsat8760 : Unsatisfiable (PosFin 65) f8760 := by
  apply lratCheckerSound f8760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8760
  · intro a ha; simp [p8760] at ha; subst a; trivial
  · exact checked8760
theorem derived8760 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8760 := by
  apply localUnsat_implies_entails f8760 [c8758, c8743, c8759, c8746, c5485, c5476] c8760 unsat8760 (by rfl) a
  have h0 : Entails.eval a c8758 := derived8758 a h
  have h1 : Entails.eval a c8743 := derived8743 a h
  have h2 : Entails.eval a c8759 := derived8759 a h
  have h3 : Entails.eval a c8746 := derived8746 a h
  have h4 : Entails.eval a c5485 := h 5484 (by decide)
  have h5 : Entails.eval a c5476 := h 5475 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8761 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨27, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8761 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c578, some c575, some c595, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8761 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8761 : lratChecker f8761 p8761 = .success := by decide +kernel
theorem unsat8761 : Unsatisfiable (PosFin 65) f8761 := by
  apply lratCheckerSound f8761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8761
  · intro a ha; simp [p8761] at ha; subst a; trivial
  · exact checked8761
theorem derived8761 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8761 := by
  apply localUnsat_implies_entails f8761 [c578, c575, c595] c8761 unsat8761 (by rfl) a
  have h0 : Entails.eval a c578 := h 577 (by decide)
  have h1 : Entails.eval a c575 := h 574 (by decide)
  have h2 : Entails.eval a c595 := h 594 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8762 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨32, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8762 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5491, some c5492, some c5481, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8762 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8762 : lratChecker f8762 p8762 = .success := by decide +kernel
theorem unsat8762 : Unsatisfiable (PosFin 65) f8762 := by
  apply lratCheckerSound f8762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8762
  · intro a ha; simp [p8762] at ha; subst a; trivial
  · exact checked8762
theorem derived8762 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8762 := by
  apply localUnsat_implies_entails f8762 [c5491, c5492, c5481] c8762 unsat8762 (by rfl) a
  have h0 : Entails.eval a c5491 := h 5490 (by decide)
  have h1 : Entails.eval a c5492 := h 5491 (by decide)
  have h2 : Entails.eval a c5481 := h 5480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8763 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8763 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8762, some c151, some c152, some c150, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8763 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8763 : lratChecker f8763 p8763 = .success := by decide +kernel
theorem unsat8763 : Unsatisfiable (PosFin 65) f8763 := by
  apply lratCheckerSound f8763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8763
  · intro a ha; simp [p8763] at ha; subst a; trivial
  · exact checked8763
theorem derived8763 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8763 := by
  apply localUnsat_implies_entails f8763 [c8762, c151, c152, c150] c8763 unsat8763 (by rfl) a
  have h0 : Entails.eval a c8762 := derived8762 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8764 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8764 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8752, some c5489, some c5486, some c562, some c5465, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8764 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8764 : lratChecker f8764 p8764 = .success := by decide +kernel
theorem unsat8764 : Unsatisfiable (PosFin 65) f8764 := by
  apply lratCheckerSound f8764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8764
  · intro a ha; simp [p8764] at ha; subst a; trivial
  · exact checked8764
theorem derived8764 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8764 := by
  apply localUnsat_implies_entails f8764 [c8752, c5489, c5486, c562, c5465] c8764 unsat8764 (by rfl) a
  have h0 : Entails.eval a c8752 := derived8752 a h
  have h1 : Entails.eval a c5489 := h 5488 (by decide)
  have h2 : Entails.eval a c5486 := h 5485 (by decide)
  have h3 : Entails.eval a c562 := h 561 (by decide)
  have h4 : Entails.eval a c5465 := h 5464 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8765 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8765 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8734, some c8741, some c8755, some c8760, some c8761, some c8763, some c8764, some c179, some c176, some c146, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8765 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8765 : lratChecker f8765 p8765 = .success := by decide +kernel
theorem unsat8765 : Unsatisfiable (PosFin 65) f8765 := by
  apply lratCheckerSound f8765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8765
  · intro a ha; simp [p8765] at ha; subst a; trivial
  · exact checked8765
theorem derived8765 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8765 := by
  apply localUnsat_implies_entails f8765 [c8686, c8734, c8741, c8755, c8760, c8761, c8763, c8764, c179, c176, c146] c8765 unsat8765 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8734 := derived8734 a h
  have h2 : Entails.eval a c8741 := derived8741 a h
  have h3 : Entails.eval a c8755 := derived8755 a h
  have h4 : Entails.eval a c8760 := derived8760 a h
  have h5 : Entails.eval a c8761 := derived8761 a h
  have h6 : Entails.eval a c8763 := derived8763 a h
  have h7 : Entails.eval a c8764 := derived8764 a h
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8766 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8766 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c852, some c5485, some c5488, some c828, some c1284, some c3982, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8766 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8766 : lratChecker f8766 p8766 = .success := by decide +kernel
theorem unsat8766 : Unsatisfiable (PosFin 65) f8766 := by
  apply lratCheckerSound f8766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8766
  · intro a ha; simp [p8766] at ha; subst a; trivial
  · exact checked8766
theorem derived8766 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8766 := by
  apply localUnsat_implies_entails f8766 [c852, c5485, c5488, c828, c1284, c3982] c8766 unsat8766 (by rfl) a
  have h0 : Entails.eval a c852 := h 851 (by decide)
  have h1 : Entails.eval a c5485 := h 5484 (by decide)
  have h2 : Entails.eval a c5488 := h 5487 (by decide)
  have h3 : Entails.eval a c828 := h 827 (by decide)
  have h4 : Entails.eval a c1284 := h 1283 (by decide)
  have h5 : Entails.eval a c3982 := h 3981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8767 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8767 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8734, some c8686, some c8741, some c8755, some c8760, some c8761, some c8763, some c8765, some c8766, some c175, some c178, some c156, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8767 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8767 : lratChecker f8767 p8767 = .success := by decide +kernel
theorem unsat8767 : Unsatisfiable (PosFin 65) f8767 := by
  apply lratCheckerSound f8767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8767
  · intro a ha; simp [p8767] at ha; subst a; trivial
  · exact checked8767
theorem derived8767 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8767 := by
  apply localUnsat_implies_entails f8767 [c8734, c8686, c8741, c8755, c8760, c8761, c8763, c8765, c8766, c175, c178, c156] c8767 unsat8767 (by rfl) a
  have h0 : Entails.eval a c8734 := derived8734 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8741 := derived8741 a h
  have h3 : Entails.eval a c8755 := derived8755 a h
  have h4 : Entails.eval a c8760 := derived8760 a h
  have h5 : Entails.eval a c8761 := derived8761 a h
  have h6 : Entails.eval a c8763 := derived8763 a h
  have h7 : Entails.eval a c8765 := derived8765 a h
  have h8 : Entails.eval a c8766 := derived8766 a h
  have h9 : Entails.eval a c175 := h 174 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8768 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8768 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8697, some c8721, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8768 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8768 : lratChecker f8768 p8768 = .success := by decide +kernel
theorem unsat8768 : Unsatisfiable (PosFin 65) f8768 := by
  apply lratCheckerSound f8768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8768
  · intro a ha; simp [p8768] at ha; subst a; trivial
  · exact checked8768
theorem derived8768 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8768 := by
  apply localUnsat_implies_entails f8768 [c8697, c8721] c8768 unsat8768 (by rfl) a
  have h0 : Entails.eval a c8697 := derived8697 a h
  have h1 : Entails.eval a c8721 := derived8721 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8769 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8769 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8722, some c8724, some c8715, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8769 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8769 : lratChecker f8769 p8769 = .success := by decide +kernel
theorem unsat8769 : Unsatisfiable (PosFin 65) f8769 := by
  apply lratCheckerSound f8769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8769
  · intro a ha; simp [p8769] at ha; subst a; trivial
  · exact checked8769
theorem derived8769 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8769 := by
  apply localUnsat_implies_entails f8769 [c8722, c8724, c8715] c8769 unsat8769 (by rfl) a
  have h0 : Entails.eval a c8722 := derived8722 a h
  have h1 : Entails.eval a c8724 := derived8724 a h
  have h2 : Entails.eval a c8715 := derived8715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8770 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8770 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8768, some c8769, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8770 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8770 : lratChecker f8770 p8770 = .success := by decide +kernel
theorem unsat8770 : Unsatisfiable (PosFin 65) f8770 := by
  apply lratCheckerSound f8770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8770
  · intro a ha; simp [p8770] at ha; subst a; trivial
  · exact checked8770
theorem derived8770 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8770 := by
  apply localUnsat_implies_entails f8770 [c8768, c8769] c8770 unsat8770 (by rfl) a
  have h0 : Entails.eval a c8768 := derived8768 a h
  have h1 : Entails.eval a c8769 := derived8769 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8771 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8771 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c629, some c5974, some c8757, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8771 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8771 : lratChecker f8771 p8771 = .success := by decide +kernel
theorem unsat8771 : Unsatisfiable (PosFin 65) f8771 := by
  apply lratCheckerSound f8771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8771
  · intro a ha; simp [p8771] at ha; subst a; trivial
  · exact checked8771
theorem derived8771 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8771 := by
  apply localUnsat_implies_entails f8771 [c629, c5974, c8757] c8771 unsat8771 (by rfl) a
  have h0 : Entails.eval a c629 := h 628 (by decide)
  have h1 : Entails.eval a c5974 := h 5973 (by decide)
  have h2 : Entails.eval a c8757 := derived8757 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8772 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8772 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1212, some c4902, some c298, some c5951, some c6193, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8772 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8772 : lratChecker f8772 p8772 = .success := by decide +kernel
theorem unsat8772 : Unsatisfiable (PosFin 65) f8772 := by
  apply lratCheckerSound f8772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8772
  · intro a ha; simp [p8772] at ha; subst a; trivial
  · exact checked8772
theorem derived8772 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8772 := by
  apply localUnsat_implies_entails f8772 [c1212, c4902, c298, c5951, c6193] c8772 unsat8772 (by rfl) a
  have h0 : Entails.eval a c1212 := h 1211 (by decide)
  have h1 : Entails.eval a c4902 := h 4901 (by decide)
  have h2 : Entails.eval a c298 := h 297 (by decide)
  have h3 : Entails.eval a c5951 := h 5950 (by decide)
  have h4 : Entails.eval a c6193 := h 6192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8773 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8773 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8767, some c8734, some c8686, some c8421, some c8770, some c8771, some c8772, some c8757, some c624, some c628, some c643, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8773 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8773 : lratChecker f8773 p8773 = .success := by decide +kernel
theorem unsat8773 : Unsatisfiable (PosFin 65) f8773 := by
  apply lratCheckerSound f8773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8773
  · intro a ha; simp [p8773] at ha; subst a; trivial
  · exact checked8773
theorem derived8773 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8773 := by
  apply localUnsat_implies_entails f8773 [c8767, c8734, c8686, c8421, c8770, c8771, c8772, c8757, c624, c628, c643] c8773 unsat8773 (by rfl) a
  have h0 : Entails.eval a c8767 := derived8767 a h
  have h1 : Entails.eval a c8734 := derived8734 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8770 := derived8770 a h
  have h5 : Entails.eval a c8771 := derived8771 a h
  have h6 : Entails.eval a c8772 := derived8772 a h
  have h7 : Entails.eval a c8757 := derived8757 a h
  have h8 : Entails.eval a c624 := h 623 (by decide)
  have h9 : Entails.eval a c628 := h 627 (by decide)
  have h10 : Entails.eval a c643 := h 642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8774 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8774 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8773, some c8767, some c8734, some c8686, some c8768, some c8738, some c8715, some c8736, some c8739, some c8666, some c5459, some c5428, some c6171, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8774 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8774 : lratChecker f8774 p8774 = .success := by decide +kernel
theorem unsat8774 : Unsatisfiable (PosFin 65) f8774 := by
  apply lratCheckerSound f8774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8774
  · intro a ha; simp [p8774] at ha; subst a; trivial
  · exact checked8774
theorem derived8774 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8774 := by
  apply localUnsat_implies_entails f8774 [c8773, c8767, c8734, c8686, c8768, c8738, c8715, c8736, c8739, c8666, c5459, c5428, c6171] c8774 unsat8774 (by rfl) a
  have h0 : Entails.eval a c8773 := derived8773 a h
  have h1 : Entails.eval a c8767 := derived8767 a h
  have h2 : Entails.eval a c8734 := derived8734 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8768 := derived8768 a h
  have h5 : Entails.eval a c8738 := derived8738 a h
  have h6 : Entails.eval a c8715 := derived8715 a h
  have h7 : Entails.eval a c8736 := derived8736 a h
  have h8 : Entails.eval a c8739 := derived8739 a h
  have h9 : Entails.eval a c8666 := derived8666 a h
  have h10 : Entails.eval a c5459 := h 5458 (by decide)
  have h11 : Entails.eval a c5428 := h 5427 (by decide)
  have h12 : Entails.eval a c6171 := h 6170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8775 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8775 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8767, some c8734, some c8686, some c8773, some c8774, some c8743, some c8759, some c8746, some c5484, some c5478, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8775 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8775 : lratChecker f8775 p8775 = .success := by decide +kernel
theorem unsat8775 : Unsatisfiable (PosFin 65) f8775 := by
  apply lratCheckerSound f8775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8775
  · intro a ha; simp [p8775] at ha; subst a; trivial
  · exact checked8775
theorem derived8775 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8775 := by
  apply localUnsat_implies_entails f8775 [c8767, c8734, c8686, c8773, c8774, c8743, c8759, c8746, c5484, c5478] c8775 unsat8775 (by rfl) a
  have h0 : Entails.eval a c8767 := derived8767 a h
  have h1 : Entails.eval a c8734 := derived8734 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8773 := derived8773 a h
  have h4 : Entails.eval a c8774 := derived8774 a h
  have h5 : Entails.eval a c8743 := derived8743 a h
  have h6 : Entails.eval a c8759 := derived8759 a h
  have h7 : Entails.eval a c8746 := derived8746 a h
  have h8 : Entails.eval a c5484 := h 5483 (by decide)
  have h9 : Entails.eval a c5478 := h 5477 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8776 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8776 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8768, some c8692, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8776 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8776 : lratChecker f8776 p8776 = .success := by decide +kernel
theorem unsat8776 : Unsatisfiable (PosFin 65) f8776 := by
  apply lratCheckerSound f8776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8776
  · intro a ha; simp [p8776] at ha; subst a; trivial
  · exact checked8776
theorem derived8776 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8776 := by
  apply localUnsat_implies_entails f8776 [c8768, c8692] c8776 unsat8776 (by rfl) a
  have h0 : Entails.eval a c8768 := derived8768 a h
  have h1 : Entails.eval a c8692 := derived8692 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8777 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨1, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8777 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c579, some c8761, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p8777 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8777 : lratChecker f8777 p8777 = .success := by decide +kernel
theorem unsat8777 : Unsatisfiable (PosFin 65) f8777 := by
  apply lratCheckerSound f8777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8777
  · intro a ha; simp [p8777] at ha; subst a; trivial
  · exact checked8777
theorem derived8777 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8777 := by
  apply localUnsat_implies_entails f8777 [c579, c8761] c8777 unsat8777 (by rfl) a
  have h0 : Entails.eval a c579 := h 578 (by decide)
  have h1 : Entails.eval a c8761 := derived8761 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8778 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8778 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c164, some c165, some c185, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8778 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8778 : lratChecker f8778 p8778 = .success := by decide +kernel
theorem unsat8778 : Unsatisfiable (PosFin 65) f8778 := by
  apply lratCheckerSound f8778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8778
  · intro a ha; simp [p8778] at ha; subst a; trivial
  · exact checked8778
theorem derived8778 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8778 := by
  apply localUnsat_implies_entails f8778 [c164, c165, c185] c8778 unsat8778 (by rfl) a
  have h0 : Entails.eval a c164 := h 163 (by decide)
  have h1 : Entails.eval a c165 := h 164 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8779 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8779 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8734, some c8767, some c8775, some c8776, some c8777, some c8763, some c8778, some c5497, some c8764, some c5484, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8779 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8779 : lratChecker f8779 p8779 = .success := by decide +kernel
theorem unsat8779 : Unsatisfiable (PosFin 65) f8779 := by
  apply lratCheckerSound f8779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8779
  · intro a ha; simp [p8779] at ha; subst a; trivial
  · exact checked8779
theorem derived8779 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8779 := by
  apply localUnsat_implies_entails f8779 [c8686, c8734, c8767, c8775, c8776, c8777, c8763, c8778, c5497, c8764, c5484] c8779 unsat8779 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8734 := derived8734 a h
  have h2 : Entails.eval a c8767 := derived8767 a h
  have h3 : Entails.eval a c8775 := derived8775 a h
  have h4 : Entails.eval a c8776 := derived8776 a h
  have h5 : Entails.eval a c8777 := derived8777 a h
  have h6 : Entails.eval a c8763 := derived8763 a h
  have h7 : Entails.eval a c8778 := derived8778 a h
  have h8 : Entails.eval a c5497 := h 5496 (by decide)
  have h9 : Entails.eval a c8764 := derived8764 a h
  have h10 : Entails.eval a c5484 := h 5483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8780 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨50, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8780 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1210, some c1231, some c1211, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8780 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8780 : lratChecker f8780 p8780 = .success := by decide +kernel
theorem unsat8780 : Unsatisfiable (PosFin 65) f8780 := by
  apply lratCheckerSound f8780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8780
  · intro a ha; simp [p8780] at ha; subst a; trivial
  · exact checked8780
theorem derived8780 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8780 := by
  apply localUnsat_implies_entails f8780 [c1210, c1231, c1211] c8780 unsat8780 (by rfl) a
  have h0 : Entails.eval a c1210 := h 1209 (by decide)
  have h1 : Entails.eval a c1231 := h 1230 (by decide)
  have h2 : Entails.eval a c1211 := h 1210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8781 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨55, by decide⟩, false), (⟨32, by decide⟩, false), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8781 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8769, some c8706, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8781 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8781 : lratChecker f8781 p8781 = .success := by decide +kernel
theorem unsat8781 : Unsatisfiable (PosFin 65) f8781 := by
  apply lratCheckerSound f8781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8781
  · intro a ha; simp [p8781] at ha; subst a; trivial
  · exact checked8781
theorem derived8781 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8781 := by
  apply localUnsat_implies_entails f8781 [c8769, c8706] c8781 unsat8781 (by rfl) a
  have h0 : Entails.eval a c8769 := derived8769 a h
  have h1 : Entails.eval a c8706 := derived8706 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8782 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨55, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8782 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8779, some c8780, some c8269, some c8421, some c1076, some c630, some c1131, some c4617, some c5994, some c6221, some c6257, some c4901, some c4454, some c1012, some c6005, some c6182, some c305, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8782 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8782 : lratChecker f8782 p8782 = .success := by decide +kernel
theorem unsat8782 : Unsatisfiable (PosFin 65) f8782 := by
  apply lratCheckerSound f8782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8782
  · intro a ha; simp [p8782] at ha; subst a; trivial
  · exact checked8782
theorem derived8782 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8782 := by
  apply localUnsat_implies_entails f8782 [c8686, c8779, c8780, c8269, c8421, c1076, c630, c1131, c4617, c5994, c6221, c6257, c4901, c4454, c1012, c6005, c6182, c305] c8782 unsat8782 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8779 := derived8779 a h
  have h2 : Entails.eval a c8780 := derived8780 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c1076 := h 1075 (by decide)
  have h6 : Entails.eval a c630 := h 629 (by decide)
  have h7 : Entails.eval a c1131 := h 1130 (by decide)
  have h8 : Entails.eval a c4617 := h 4616 (by decide)
  have h9 : Entails.eval a c5994 := h 5993 (by decide)
  have h10 : Entails.eval a c6221 := h 6220 (by decide)
  have h11 : Entails.eval a c6257 := h 6256 (by decide)
  have h12 : Entails.eval a c4901 := h 4900 (by decide)
  have h13 : Entails.eval a c4454 := h 4453 (by decide)
  have h14 : Entails.eval a c1012 := h 1011 (by decide)
  have h15 : Entails.eval a c6005 := h 6004 (by decide)
  have h16 : Entails.eval a c6182 := h 6181 (by decide)
  have h17 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8783 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8783 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c1267, some c8779, some c8780, some c4457, some c8782, some c8781, some c8269, some c8690, some c6117, some c5460, some c8715, some c221, some c217, some c189, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8783 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8783 : lratChecker f8783 p8783 = .success := by decide +kernel
theorem unsat8783 : Unsatisfiable (PosFin 65) f8783 := by
  apply lratCheckerSound f8783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8783
  · intro a ha; simp [p8783] at ha; subst a; trivial
  · exact checked8783
theorem derived8783 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8783 := by
  apply localUnsat_implies_entails f8783 [c8686, c1267, c8779, c8780, c4457, c8782, c8781, c8269, c8690, c6117, c5460, c8715, c221, c217, c189] c8783 unsat8783 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c1267 := h 1266 (by decide)
  have h2 : Entails.eval a c8779 := derived8779 a h
  have h3 : Entails.eval a c8780 := derived8780 a h
  have h4 : Entails.eval a c4457 := h 4456 (by decide)
  have h5 : Entails.eval a c8782 := derived8782 a h
  have h6 : Entails.eval a c8781 := derived8781 a h
  have h7 : Entails.eval a c8269 := derived8269 a h
  have h8 : Entails.eval a c8690 := derived8690 a h
  have h9 : Entails.eval a c6117 := h 6116 (by decide)
  have h10 : Entails.eval a c5460 := h 5459 (by decide)
  have h11 : Entails.eval a c8715 := derived8715 a h
  have h12 : Entails.eval a c221 := h 220 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8784 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨55, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8784 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8782, some c8686, some c8779, some c8780, some c8781, some c8269, some c8783, some c8691, some c6208, some c8739, some c6091, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8784 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8784 : lratChecker f8784 p8784 = .success := by decide +kernel
theorem unsat8784 : Unsatisfiable (PosFin 65) f8784 := by
  apply lratCheckerSound f8784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8784
  · intro a ha; simp [p8784] at ha; subst a; trivial
  · exact checked8784
theorem derived8784 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8784 := by
  apply localUnsat_implies_entails f8784 [c8782, c8686, c8779, c8780, c8781, c8269, c8783, c8691, c6208, c8739, c6091] c8784 unsat8784 (by rfl) a
  have h0 : Entails.eval a c8782 := derived8782 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8779 := derived8779 a h
  have h3 : Entails.eval a c8780 := derived8780 a h
  have h4 : Entails.eval a c8781 := derived8781 a h
  have h5 : Entails.eval a c8269 := derived8269 a h
  have h6 : Entails.eval a c8783 := derived8783 a h
  have h7 : Entails.eval a c8691 := derived8691 a h
  have h8 : Entails.eval a c6208 := h 6207 (by decide)
  have h9 : Entails.eval a c8739 := derived8739 a h
  have h10 : Entails.eval a c6091 := h 6090 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8785 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8785 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8737, some c623, some c610, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8785 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8785 : lratChecker f8785 p8785 = .success := by decide +kernel
theorem unsat8785 : Unsatisfiable (PosFin 65) f8785 := by
  apply lratCheckerSound f8785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8785
  · intro a ha; simp [p8785] at ha; subst a; trivial
  · exact checked8785
theorem derived8785 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8785 := by
  apply localUnsat_implies_entails f8785 [c8737, c623, c610] c8785 unsat8785 (by rfl) a
  have h0 : Entails.eval a c8737 := derived8737 a h
  have h1 : Entails.eval a c623 := h 622 (by decide)
  have h2 : Entails.eval a c610 := h 609 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8786 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8786 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8779, some c8780, some c8781, some c8782, some c8784, some c8785, some c8715, some c8716, some c8740, some c5459, some c5428, some c6171, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8786 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8786 : lratChecker f8786 p8786 = .success := by decide +kernel
theorem unsat8786 : Unsatisfiable (PosFin 65) f8786 := by
  apply lratCheckerSound f8786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8786
  · intro a ha; simp [p8786] at ha; subst a; trivial
  · exact checked8786
theorem derived8786 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8786 := by
  apply localUnsat_implies_entails f8786 [c8686, c8779, c8780, c8781, c8782, c8784, c8785, c8715, c8716, c8740, c5459, c5428, c6171] c8786 unsat8786 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8779 := derived8779 a h
  have h2 : Entails.eval a c8780 := derived8780 a h
  have h3 : Entails.eval a c8781 := derived8781 a h
  have h4 : Entails.eval a c8782 := derived8782 a h
  have h5 : Entails.eval a c8784 := derived8784 a h
  have h6 : Entails.eval a c8785 := derived8785 a h
  have h7 : Entails.eval a c8715 := derived8715 a h
  have h8 : Entails.eval a c8716 := derived8716 a h
  have h9 : Entails.eval a c8740 := derived8740 a h
  have h10 : Entails.eval a c5459 := h 5458 (by decide)
  have h11 : Entails.eval a c5428 := h 5427 (by decide)
  have h12 : Entails.eval a c6171 := h 6170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8787 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨55, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨56, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8787 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8697, some c5996, some c6000, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8787 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8787 : lratChecker f8787 p8787 = .success := by decide +kernel
theorem unsat8787 : Unsatisfiable (PosFin 65) f8787 := by
  apply lratCheckerSound f8787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8787
  · intro a ha; simp [p8787] at ha; subst a; trivial
  · exact checked8787
theorem derived8787 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8787 := by
  apply localUnsat_implies_entails f8787 [c8697, c5996, c6000] c8787 unsat8787 (by rfl) a
  have h0 : Entails.eval a c8697 := derived8697 a h
  have h1 : Entails.eval a c5996 := h 5995 (by decide)
  have h2 : Entails.eval a c6000 := h 5999 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8788 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨55, by decide⟩, true), (⟨32, by decide⟩, false), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8788 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1269, some c5906, some c4457, some c4725, some c6092, some c6142, some c346, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8788 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8788 : lratChecker f8788 p8788 = .success := by decide +kernel
theorem unsat8788 : Unsatisfiable (PosFin 65) f8788 := by
  apply lratCheckerSound f8788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8788
  · intro a ha; simp [p8788] at ha; subst a; trivial
  · exact checked8788
theorem derived8788 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8788 := by
  apply localUnsat_implies_entails f8788 [c1269, c5906, c4457, c4725, c6092, c6142, c346] c8788 unsat8788 (by rfl) a
  have h0 : Entails.eval a c1269 := h 1268 (by decide)
  have h1 : Entails.eval a c5906 := h 5905 (by decide)
  have h2 : Entails.eval a c4457 := h 4456 (by decide)
  have h3 : Entails.eval a c4725 := h 4724 (by decide)
  have h4 : Entails.eval a c6092 := h 6091 (by decide)
  have h5 : Entails.eval a c6142 := h 6141 (by decide)
  have h6 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8789 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8789 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8779, some c8780, some c8786, some c8787, some c8769, some c8788, some c8785, some c8715, some c8666, some c5459, some c5428, some c6171, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8789 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8789 : lratChecker f8789 p8789 = .success := by decide +kernel
theorem unsat8789 : Unsatisfiable (PosFin 65) f8789 := by
  apply lratCheckerSound f8789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8789
  · intro a ha; simp [p8789] at ha; subst a; trivial
  · exact checked8789
theorem derived8789 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8789 := by
  apply localUnsat_implies_entails f8789 [c8686, c8779, c8780, c8786, c8787, c8769, c8788, c8785, c8715, c8666, c5459, c5428, c6171] c8789 unsat8789 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8779 := derived8779 a h
  have h2 : Entails.eval a c8780 := derived8780 a h
  have h3 : Entails.eval a c8786 := derived8786 a h
  have h4 : Entails.eval a c8787 := derived8787 a h
  have h5 : Entails.eval a c8769 := derived8769 a h
  have h6 : Entails.eval a c8788 := derived8788 a h
  have h7 : Entails.eval a c8785 := derived8785 a h
  have h8 : Entails.eval a c8715 := derived8715 a h
  have h9 : Entails.eval a c8666 := derived8666 a h
  have h10 : Entails.eval a c5459 := h 5458 (by decide)
  have h11 : Entails.eval a c5428 := h 5427 (by decide)
  have h12 : Entails.eval a c6171 := h 6170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8790 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8790 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8695, some c8743, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8790 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8790 : lratChecker f8790 p8790 = .success := by decide +kernel
theorem unsat8790 : Unsatisfiable (PosFin 65) f8790 := by
  apply lratCheckerSound f8790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8790
  · intro a ha; simp [p8790] at ha; subst a; trivial
  · exact checked8790
theorem derived8790 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8790 := by
  apply localUnsat_implies_entails f8790 [c8695, c8743] c8790 unsat8790 (by rfl) a
  have h0 : Entails.eval a c8695 := derived8695 a h
  have h1 : Entails.eval a c8743 := derived8743 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8791 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8791 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c159, some c145, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8791 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8791 : lratChecker f8791 p8791 = .success := by decide +kernel
theorem unsat8791 : Unsatisfiable (PosFin 65) f8791 := by
  apply lratCheckerSound f8791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8791
  · intro a ha; simp [p8791] at ha; subst a; trivial
  · exact checked8791
theorem derived8791 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8791 := by
  apply localUnsat_implies_entails f8791 [c159, c145] c8791 unsat8791 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8792 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8792 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8789, some c8686, some c8779, some c8780, some c8421, some c8790, some c8719, some c8791, some c5496, some c5476, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8792 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8792 : lratChecker f8792 p8792 = .success := by decide +kernel
theorem unsat8792 : Unsatisfiable (PosFin 65) f8792 := by
  apply lratCheckerSound f8792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8792
  · intro a ha; simp [p8792] at ha; subst a; trivial
  · exact checked8792
theorem derived8792 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8792 := by
  apply localUnsat_implies_entails f8792 [c8789, c8686, c8779, c8780, c8421, c8790, c8719, c8791, c5496, c5476] c8792 unsat8792 (by rfl) a
  have h0 : Entails.eval a c8789 := derived8789 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8779 := derived8779 a h
  have h3 : Entails.eval a c8780 := derived8780 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c8790 := derived8790 a h
  have h6 : Entails.eval a c8719 := derived8719 a h
  have h7 : Entails.eval a c8791 := derived8791 a h
  have h8 : Entails.eval a c5496 := h 5495 (by decide)
  have h9 : Entails.eval a c5476 := h 5475 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8793 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨55, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8793 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8695, some c8756, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8793 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8793 : lratChecker f8793 p8793 = .success := by decide +kernel
theorem unsat8793 : Unsatisfiable (PosFin 65) f8793 := by
  apply lratCheckerSound f8793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8793
  · intro a ha; simp [p8793] at ha; subst a; trivial
  · exact checked8793
theorem derived8793 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8793 := by
  apply localUnsat_implies_entails f8793 [c8695, c8756] c8793 unsat8793 (by rfl) a
  have h0 : Entails.eval a c8695 := derived8695 a h
  have h1 : Entails.eval a c8756 := derived8756 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8794 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8794 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8701, some c8708, some c8714, some c8707, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8794 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8794 : lratChecker f8794 p8794 = .success := by decide +kernel
theorem unsat8794 : Unsatisfiable (PosFin 65) f8794 := by
  apply lratCheckerSound f8794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8794
  · intro a ha; simp [p8794] at ha; subst a; trivial
  · exact checked8794
theorem derived8794 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8794 := by
  apply localUnsat_implies_entails f8794 [c8701, c8708, c8714, c8707] c8794 unsat8794 (by rfl) a
  have h0 : Entails.eval a c8701 := derived8701 a h
  have h1 : Entails.eval a c8708 := derived8708 a h
  have h2 : Entails.eval a c8714 := derived8714 a h
  have h3 : Entails.eval a c8707 := derived8707 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8795 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8795 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8713, some c5394, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8795 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8795 : lratChecker f8795 p8795 = .success := by decide +kernel
theorem unsat8795 : Unsatisfiable (PosFin 65) f8795 := by
  apply lratCheckerSound f8795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8795
  · intro a ha; simp [p8795] at ha; subst a; trivial
  · exact checked8795
theorem derived8795 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8795 := by
  apply localUnsat_implies_entails f8795 [c8713, c5394] c8795 unsat8795 (by rfl) a
  have h0 : Entails.eval a c8713 := derived8713 a h
  have h1 : Entails.eval a c5394 := h 5393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8796 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8796 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8789, some c8686, some c8779, some c8780, some c8792, some c8706, some c8793, some c8794, some c8718, some c8791, some c8795, some c624, some c628, some c643, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8796 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8796 : lratChecker f8796 p8796 = .success := by decide +kernel
theorem unsat8796 : Unsatisfiable (PosFin 65) f8796 := by
  apply lratCheckerSound f8796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8796
  · intro a ha; simp [p8796] at ha; subst a; trivial
  · exact checked8796
theorem derived8796 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8796 := by
  apply localUnsat_implies_entails f8796 [c8789, c8686, c8779, c8780, c8792, c8706, c8793, c8794, c8718, c8791, c8795, c624, c628, c643] c8796 unsat8796 (by rfl) a
  have h0 : Entails.eval a c8789 := derived8789 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8779 := derived8779 a h
  have h3 : Entails.eval a c8780 := derived8780 a h
  have h4 : Entails.eval a c8792 := derived8792 a h
  have h5 : Entails.eval a c8706 := derived8706 a h
  have h6 : Entails.eval a c8793 := derived8793 a h
  have h7 : Entails.eval a c8794 := derived8794 a h
  have h8 : Entails.eval a c8718 := derived8718 a h
  have h9 : Entails.eval a c8791 := derived8791 a h
  have h10 : Entails.eval a c8795 := derived8795 a h
  have h11 : Entails.eval a c624 := h 623 (by decide)
  have h12 : Entails.eval a c628 := h 627 (by decide)
  have h13 : Entails.eval a c643 := h 642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8797 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨55, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨56, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8797 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5974, some c8729, some c5321, some c173, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8797 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8797 : lratChecker f8797 p8797 = .success := by decide +kernel
theorem unsat8797 : Unsatisfiable (PosFin 65) f8797 := by
  apply lratCheckerSound f8797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8797
  · intro a ha; simp [p8797] at ha; subst a; trivial
  · exact checked8797
theorem derived8797 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8797 := by
  apply localUnsat_implies_entails f8797 [c5974, c8729, c5321, c173] c8797 unsat8797 (by rfl) a
  have h0 : Entails.eval a c5974 := h 5973 (by decide)
  have h1 : Entails.eval a c8729 := derived8729 a h
  have h2 : Entails.eval a c5321 := h 5320 (by decide)
  have h3 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8798 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8798 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8796, some c8789, some c8779, some c8686, some c8421, some c8797, some c8772, some c8794, some c8666, some c8795, some c624, some c628, some c643, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8798 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8798 : lratChecker f8798 p8798 = .success := by decide +kernel
theorem unsat8798 : Unsatisfiable (PosFin 65) f8798 := by
  apply lratCheckerSound f8798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8798
  · intro a ha; simp [p8798] at ha; subst a; trivial
  · exact checked8798
theorem derived8798 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8798 := by
  apply localUnsat_implies_entails f8798 [c8796, c8789, c8779, c8686, c8421, c8797, c8772, c8794, c8666, c8795, c624, c628, c643] c8798 unsat8798 (by rfl) a
  have h0 : Entails.eval a c8796 := derived8796 a h
  have h1 : Entails.eval a c8789 := derived8789 a h
  have h2 : Entails.eval a c8779 := derived8779 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c8797 := derived8797 a h
  have h6 : Entails.eval a c8772 := derived8772 a h
  have h7 : Entails.eval a c8794 := derived8794 a h
  have h8 : Entails.eval a c8666 := derived8666 a h
  have h9 : Entails.eval a c8795 := derived8795 a h
  have h10 : Entails.eval a c624 := h 623 (by decide)
  have h11 : Entails.eval a c628 := h 627 (by decide)
  have h12 : Entails.eval a c643 := h 642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8799 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8799 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5820, some c5826, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8799 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8799 : lratChecker f8799 p8799 = .success := by decide +kernel
theorem unsat8799 : Unsatisfiable (PosFin 65) f8799 := by
  apply lratCheckerSound f8799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8799
  · intro a ha; simp [p8799] at ha; subst a; trivial
  · exact checked8799
theorem derived8799 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8799 := by
  apply localUnsat_implies_entails f8799 [c5820, c5826] c8799 unsat8799 (by rfl) a
  have h0 : Entails.eval a c5820 := h 5819 (by decide)
  have h1 : Entails.eval a c5826 := h 5825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8800 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8800 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8779, some c8686, some c8789, some c8798, some c8790, some c8799, some c8791, some c5496, some c5476, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8800 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8800 : lratChecker f8800 p8800 = .success := by decide +kernel
theorem unsat8800 : Unsatisfiable (PosFin 65) f8800 := by
  apply lratCheckerSound f8800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8800
  · intro a ha; simp [p8800] at ha; subst a; trivial
  · exact checked8800
theorem derived8800 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8800 := by
  apply localUnsat_implies_entails f8800 [c8779, c8686, c8789, c8798, c8790, c8799, c8791, c5496, c5476] c8800 unsat8800 (by rfl) a
  have h0 : Entails.eval a c8779 := derived8779 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8789 := derived8789 a h
  have h3 : Entails.eval a c8798 := derived8798 a h
  have h4 : Entails.eval a c8790 := derived8790 a h
  have h5 : Entails.eval a c8799 := derived8799 a h
  have h6 : Entails.eval a c8791 := derived8791 a h
  have h7 : Entails.eval a c5496 := h 5495 (by decide)
  have h8 : Entails.eval a c5476 := h 5475 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8801 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨1, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8801 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c580, some c8692, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8801 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8801 : lratChecker f8801 p8801 = .success := by decide +kernel
theorem unsat8801 : Unsatisfiable (PosFin 65) f8801 := by
  apply lratCheckerSound f8801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8801
  · intro a ha; simp [p8801] at ha; subst a; trivial
  · exact checked8801
theorem derived8801 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8801 := by
  apply localUnsat_implies_entails f8801 [c580, c8692] c8801 unsat8801 (by rfl) a
  have h0 : Entails.eval a c580 := h 579 (by decide)
  have h1 : Entails.eval a c8692 := derived8692 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8802 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨55, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8802 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8800, some c8801, some c8731, some c8777, some c8763, some c8779, some c5496, some c377, some c8766, some c5483, some c5493, some c44, some c25, some c6564, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8802 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8802 : lratChecker f8802 p8802 = .success := by decide +kernel
theorem unsat8802 : Unsatisfiable (PosFin 65) f8802 := by
  apply lratCheckerSound f8802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8802
  · intro a ha; simp [p8802] at ha; subst a; trivial
  · exact checked8802
theorem derived8802 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8802 := by
  apply localUnsat_implies_entails f8802 [c8686, c8800, c8801, c8731, c8777, c8763, c8779, c5496, c377, c8766, c5483, c5493, c44, c25, c6564] c8802 unsat8802 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8800 := derived8800 a h
  have h2 : Entails.eval a c8801 := derived8801 a h
  have h3 : Entails.eval a c8731 := derived8731 a h
  have h4 : Entails.eval a c8777 := derived8777 a h
  have h5 : Entails.eval a c8763 := derived8763 a h
  have h6 : Entails.eval a c8779 := derived8779 a h
  have h7 : Entails.eval a c5496 := h 5495 (by decide)
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c8766 := derived8766 a h
  have h10 : Entails.eval a c5483 := h 5482 (by decide)
  have h11 : Entails.eval a c5493 := h 5492 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c6564 := h 6563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8803 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨53, by decide⟩, false), (⟨19, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨20, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8803 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c159, some c156, some c153, some c171, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8803 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8803 : lratChecker f8803 p8803 = .success := by decide +kernel
theorem unsat8803 : Unsatisfiable (PosFin 65) f8803 := by
  apply lratCheckerSound f8803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8803
  · intro a ha; simp [p8803] at ha; subst a; trivial
  · exact checked8803
theorem derived8803 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8803 := by
  apply localUnsat_implies_entails f8803 [c159, c156, c153, c171] c8803 unsat8803 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8804 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8804 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8421, some c8779, some c8800, some c8777, some c8801, some c8731, some c8763, some c8803, some c779, some c5496, some c5479, some c8802, some c4873, some c5493, some c1448, some c1421, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8804 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8804 : lratChecker f8804 p8804 = .success := by decide +kernel
theorem unsat8804 : Unsatisfiable (PosFin 65) f8804 := by
  apply lratCheckerSound f8804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8804
  · intro a ha; simp [p8804] at ha; subst a; trivial
  · exact checked8804
theorem derived8804 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8804 := by
  apply localUnsat_implies_entails f8804 [c8686, c8421, c8779, c8800, c8777, c8801, c8731, c8763, c8803, c779, c5496, c5479, c8802, c4873, c5493, c1448, c1421] c8804 unsat8804 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8779 := derived8779 a h
  have h3 : Entails.eval a c8800 := derived8800 a h
  have h4 : Entails.eval a c8777 := derived8777 a h
  have h5 : Entails.eval a c8801 := derived8801 a h
  have h6 : Entails.eval a c8731 := derived8731 a h
  have h7 : Entails.eval a c8763 := derived8763 a h
  have h8 : Entails.eval a c8803 := derived8803 a h
  have h9 : Entails.eval a c779 := h 778 (by decide)
  have h10 : Entails.eval a c5496 := h 5495 (by decide)
  have h11 : Entails.eval a c5479 := h 5478 (by decide)
  have h12 : Entails.eval a c8802 := derived8802 a h
  have h13 : Entails.eval a c4873 := h 4872 (by decide)
  have h14 : Entails.eval a c5493 := h 5492 (by decide)
  have h15 : Entails.eval a c1448 := h 1447 (by decide)
  have h16 : Entails.eval a c1421 := h 1420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8805 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8805 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8691, some c6249, some c6222, some c6024, some c6023, some c5728, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8805 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8805 : lratChecker f8805 p8805 = .success := by decide +kernel
theorem unsat8805 : Unsatisfiable (PosFin 65) f8805 := by
  apply lratCheckerSound f8805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8805
  · intro a ha; simp [p8805] at ha; subst a; trivial
  · exact checked8805
theorem derived8805 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8805 := by
  apply localUnsat_implies_entails f8805 [c8269, c8691, c6249, c6222, c6024, c6023, c5728] c8805 unsat8805 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8691 := derived8691 a h
  have h2 : Entails.eval a c6249 := h 6248 (by decide)
  have h3 : Entails.eval a c6222 := h 6221 (by decide)
  have h4 : Entails.eval a c6024 := h 6023 (by decide)
  have h5 : Entails.eval a c6023 := h 6022 (by decide)
  have h6 : Entails.eval a c5728 := h 5727 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8806 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8806 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8691, some c8805, some c8724, some c8690, some c8715, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8806 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8806 : lratChecker f8806 p8806 = .success := by decide +kernel
theorem unsat8806 : Unsatisfiable (PosFin 65) f8806 := by
  apply lratCheckerSound f8806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8806
  · intro a ha; simp [p8806] at ha; subst a; trivial
  · exact checked8806
theorem derived8806 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8806 := by
  apply localUnsat_implies_entails f8806 [c8269, c8691, c8805, c8724, c8690, c8715] c8806 unsat8806 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8691 := derived8691 a h
  have h2 : Entails.eval a c8805 := derived8805 a h
  have h3 : Entails.eval a c8724 := derived8724 a h
  have h4 : Entails.eval a c8690 := derived8690 a h
  have h5 : Entails.eval a c8715 := derived8715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8807 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨53, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8807 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6828, some c6889, some c6872, some c7291, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8807 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8807 : lratChecker f8807 p8807 = .success := by decide +kernel
theorem unsat8807 : Unsatisfiable (PosFin 65) f8807 := by
  apply lratCheckerSound f8807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8807
  · intro a ha; simp [p8807] at ha; subst a; trivial
  · exact checked8807
theorem derived8807 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8807 := by
  apply localUnsat_implies_entails f8807 [c6828, c6889, c6872, c7291] c8807 unsat8807 (by rfl) a
  have h0 : Entails.eval a c6828 := h 6827 (by decide)
  have h1 : Entails.eval a c6889 := h 6888 (by decide)
  have h2 : Entails.eval a c6872 := h 6871 (by decide)
  have h3 : Entails.eval a c7291 := h 7290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8808 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8808 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1267, some c1210, some c4902, some c4725, some c8806, some c144, some c33, some c269, some c5408, some c83, some c8807, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8808 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8808 : lratChecker f8808 p8808 = .success := by decide +kernel
theorem unsat8808 : Unsatisfiable (PosFin 65) f8808 := by
  apply lratCheckerSound f8808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8808
  · intro a ha; simp [p8808] at ha; subst a; trivial
  · exact checked8808
theorem derived8808 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8808 := by
  apply localUnsat_implies_entails f8808 [c1267, c1210, c4902, c4725, c8806, c144, c33, c269, c5408, c83, c8807] c8808 unsat8808 (by rfl) a
  have h0 : Entails.eval a c1267 := h 1266 (by decide)
  have h1 : Entails.eval a c1210 := h 1209 (by decide)
  have h2 : Entails.eval a c4902 := h 4901 (by decide)
  have h3 : Entails.eval a c4725 := h 4724 (by decide)
  have h4 : Entails.eval a c8806 := derived8806 a h
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c5408 := h 5407 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c8807 := derived8807 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8809 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8809 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6257, some c6068, some c5352, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8809 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8809 : lratChecker f8809 p8809 = .success := by decide +kernel
theorem unsat8809 : Unsatisfiable (PosFin 65) f8809 := by
  apply lratCheckerSound f8809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8809
  · intro a ha; simp [p8809] at ha; subst a; trivial
  · exact checked8809
theorem derived8809 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8809 := by
  apply localUnsat_implies_entails f8809 [c6257, c6068, c5352] c8809 unsat8809 (by rfl) a
  have h0 : Entails.eval a c6257 := h 6256 (by decide)
  have h1 : Entails.eval a c6068 := h 6067 (by decide)
  have h2 : Entails.eval a c5352 := h 5351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8810 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8810 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8715, some c606, some c636, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8810 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8810 : lratChecker f8810 p8810 = .success := by decide +kernel
theorem unsat8810 : Unsatisfiable (PosFin 65) f8810 := by
  apply lratCheckerSound f8810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8810
  · intro a ha; simp [p8810] at ha; subst a; trivial
  · exact checked8810
theorem derived8810 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8810 := by
  apply localUnsat_implies_entails f8810 [c8715, c606, c636] c8810 unsat8810 (by rfl) a
  have h0 : Entails.eval a c8715 := derived8715 a h
  have h1 : Entails.eval a c606 := h 605 (by decide)
  have h2 : Entails.eval a c636 := h 635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8811 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8811 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8810, some c6221, some c6257, some c6068, some c5844, some c5848, some c5734, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8811 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8811 : lratChecker f8811 p8811 = .success := by decide +kernel
theorem unsat8811 : Unsatisfiable (PosFin 65) f8811 := by
  apply lratCheckerSound f8811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8811
  · intro a ha; simp [p8811] at ha; subst a; trivial
  · exact checked8811
theorem derived8811 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8811 := by
  apply localUnsat_implies_entails f8811 [c8269, c8810, c6221, c6257, c6068, c5844, c5848, c5734] c8811 unsat8811 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8810 := derived8810 a h
  have h2 : Entails.eval a c6221 := h 6220 (by decide)
  have h3 : Entails.eval a c6257 := h 6256 (by decide)
  have h4 : Entails.eval a c6068 := h 6067 (by decide)
  have h5 : Entails.eval a c5844 := h 5843 (by decide)
  have h6 : Entails.eval a c5848 := h 5847 (by decide)
  have h7 : Entails.eval a c5734 := h 5733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8812 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8812 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c614, some c615, some c609, some c641, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8812 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8812 : lratChecker f8812 p8812 = .success := by decide +kernel
theorem unsat8812 : Unsatisfiable (PosFin 65) f8812 := by
  apply lratCheckerSound f8812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8812
  · intro a ha; simp [p8812] at ha; subst a; trivial
  · exact checked8812
theorem derived8812 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8812 := by
  apply localUnsat_implies_entails f8812 [c614, c615, c609, c641] c8812 unsat8812 (by rfl) a
  have h0 : Entails.eval a c614 := h 613 (by decide)
  have h1 : Entails.eval a c615 := h 614 (by decide)
  have h2 : Entails.eval a c609 := h 608 (by decide)
  have h3 : Entails.eval a c641 := h 640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8813 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8813 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8724, some c8715, some c8812, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8813 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8813 : lratChecker f8813 p8813 = .success := by decide +kernel
theorem unsat8813 : Unsatisfiable (PosFin 65) f8813 := by
  apply lratCheckerSound f8813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8813
  · intro a ha; simp [p8813] at ha; subst a; trivial
  · exact checked8813
theorem derived8813 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8813 := by
  apply localUnsat_implies_entails f8813 [c8724, c8715, c8812] c8813 unsat8813 (by rfl) a
  have h0 : Entails.eval a c8724 := derived8724 a h
  have h1 : Entails.eval a c8715 := derived8715 a h
  have h2 : Entails.eval a c8812 := derived8812 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8814 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8814 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8808, some c8813, some c8810, some c8811, some c6257, some c6068, some c5844, some c5848, some c8809, some c158, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8814 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8814 : lratChecker f8814 p8814 = .success := by decide +kernel
theorem unsat8814 : Unsatisfiable (PosFin 65) f8814 := by
  apply lratCheckerSound f8814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8814
  · intro a ha; simp [p8814] at ha; subst a; trivial
  · exact checked8814
theorem derived8814 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8814 := by
  apply localUnsat_implies_entails f8814 [c8269, c8808, c8813, c8810, c8811, c6257, c6068, c5844, c5848, c8809, c158] c8814 unsat8814 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8808 := derived8808 a h
  have h2 : Entails.eval a c8813 := derived8813 a h
  have h3 : Entails.eval a c8810 := derived8810 a h
  have h4 : Entails.eval a c8811 := derived8811 a h
  have h5 : Entails.eval a c6257 := h 6256 (by decide)
  have h6 : Entails.eval a c6068 := h 6067 (by decide)
  have h7 : Entails.eval a c5844 := h 5843 (by decide)
  have h8 : Entails.eval a c5848 := h 5847 (by decide)
  have h9 : Entails.eval a c8809 := derived8809 a h
  have h10 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8815 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8815 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6151, some c5784, some c269, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8815 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8815 : lratChecker f8815 p8815 = .success := by decide +kernel
theorem unsat8815 : Unsatisfiable (PosFin 65) f8815 := by
  apply lratCheckerSound f8815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8815
  · intro a ha; simp [p8815] at ha; subst a; trivial
  · exact checked8815
theorem derived8815 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8815 := by
  apply localUnsat_implies_entails f8815 [c6151, c5784, c269] c8815 unsat8815 (by rfl) a
  have h0 : Entails.eval a c6151 := h 6150 (by decide)
  have h1 : Entails.eval a c5784 := h 5783 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8816 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8816 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c1267, some c1210, some c4725, some c8815, some c6232, some c6222, some c5460, some c8690, some c6117, some c5299, some c136, some c5611, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8816 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8816 : lratChecker f8816 p8816 = .success := by decide +kernel
theorem unsat8816 : Unsatisfiable (PosFin 65) f8816 := by
  apply lratCheckerSound f8816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8816
  · intro a ha; simp [p8816] at ha; subst a; trivial
  · exact checked8816
theorem derived8816 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8816 := by
  apply localUnsat_implies_entails f8816 [c8269, c1267, c1210, c4725, c8815, c6232, c6222, c5460, c8690, c6117, c5299, c136, c5611] c8816 unsat8816 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c1267 := h 1266 (by decide)
  have h2 : Entails.eval a c1210 := h 1209 (by decide)
  have h3 : Entails.eval a c4725 := h 4724 (by decide)
  have h4 : Entails.eval a c8815 := derived8815 a h
  have h5 : Entails.eval a c6232 := h 6231 (by decide)
  have h6 : Entails.eval a c6222 := h 6221 (by decide)
  have h7 : Entails.eval a c5460 := h 5459 (by decide)
  have h8 : Entails.eval a c8690 := derived8690 a h
  have h9 : Entails.eval a c6117 := h 6116 (by decide)
  have h10 : Entails.eval a c5299 := h 5298 (by decide)
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c5611 := h 5610 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8817 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8817 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6221, some c6257, some c5933, some c5934, some c5734, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8817 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8817 : lratChecker f8817 p8817 = .success := by decide +kernel
theorem unsat8817 : Unsatisfiable (PosFin 65) f8817 := by
  apply lratCheckerSound f8817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8817
  · intro a ha; simp [p8817] at ha; subst a; trivial
  · exact checked8817
theorem derived8817 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8817 := by
  apply localUnsat_implies_entails f8817 [c8269, c6221, c6257, c5933, c5934, c5734] c8817 unsat8817 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6221 := h 6220 (by decide)
  have h2 : Entails.eval a c6257 := h 6256 (by decide)
  have h3 : Entails.eval a c5933 := h 5932 (by decide)
  have h4 : Entails.eval a c5934 := h 5933 (by decide)
  have h5 : Entails.eval a c5734 := h 5733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8818 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8818 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c644, some c646, some c627, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8818 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8818 : lratChecker f8818 p8818 = .success := by decide +kernel
theorem unsat8818 : Unsatisfiable (PosFin 65) f8818 := by
  apply lratCheckerSound f8818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8818
  · intro a ha; simp [p8818] at ha; subst a; trivial
  · exact checked8818
theorem derived8818 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8818 := by
  apply localUnsat_implies_entails f8818 [c644, c646, c627] c8818 unsat8818 (by rfl) a
  have h0 : Entails.eval a c644 := h 643 (by decide)
  have h1 : Entails.eval a c646 := h 645 (by decide)
  have h2 : Entails.eval a c627 := h 626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8819 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8819 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8818, some c6221, some c6257, some c6150, some c5933, some c5934, some c8817, some c1259, some c1194, some c5926, some c4710, some c277, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8819 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8819 : lratChecker f8819 p8819 = .success := by decide +kernel
theorem unsat8819 : Unsatisfiable (PosFin 65) f8819 := by
  apply lratCheckerSound f8819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8819
  · intro a ha; simp [p8819] at ha; subst a; trivial
  · exact checked8819
theorem derived8819 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8819 := by
  apply localUnsat_implies_entails f8819 [c8269, c8818, c6221, c6257, c6150, c5933, c5934, c8817, c1259, c1194, c5926, c4710, c277] c8819 unsat8819 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8818 := derived8818 a h
  have h2 : Entails.eval a c6221 := h 6220 (by decide)
  have h3 : Entails.eval a c6257 := h 6256 (by decide)
  have h4 : Entails.eval a c6150 := h 6149 (by decide)
  have h5 : Entails.eval a c5933 := h 5932 (by decide)
  have h6 : Entails.eval a c5934 := h 5933 (by decide)
  have h7 : Entails.eval a c8817 := derived8817 a h
  have h8 : Entails.eval a c1259 := h 1258 (by decide)
  have h9 : Entails.eval a c1194 := h 1193 (by decide)
  have h10 : Entails.eval a c5926 := h 5925 (by decide)
  have h11 : Entails.eval a c4710 := h 4709 (by decide)
  have h12 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8820 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨51, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8820 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5459, some c5428, some c6171, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8820 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8820 : lratChecker f8820 p8820 = .success := by decide +kernel
theorem unsat8820 : Unsatisfiable (PosFin 65) f8820 := by
  apply lratCheckerSound f8820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8820
  · intro a ha; simp [p8820] at ha; subst a; trivial
  · exact checked8820
theorem derived8820 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8820 := by
  apply localUnsat_implies_entails f8820 [c5459, c5428, c6171] c8820 unsat8820 (by rfl) a
  have h0 : Entails.eval a c5459 := h 5458 (by decide)
  have h1 : Entails.eval a c5428 := h 5427 (by decide)
  have h2 : Entails.eval a c6171 := h 6170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8821 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8821 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8737, some c8820, some c126, some c124, some c122, some c140, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8821 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8821 : lratChecker f8821 p8821 = .success := by decide +kernel
theorem unsat8821 : Unsatisfiable (PosFin 65) f8821 := by
  apply lratCheckerSound f8821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8821
  · intro a ha; simp [p8821] at ha; subst a; trivial
  · exact checked8821
theorem derived8821 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8821 := by
  apply localUnsat_implies_entails f8821 [c8269, c8737, c8820, c126, c124, c122, c140] c8821 unsat8821 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8737 := derived8737 a h
  have h2 : Entails.eval a c8820 := derived8820 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8822 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8822 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8804, some c8686, some c8421, some c8814, some c8816, some c8819, some c8821, some c8715, some c8812, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8822 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8822 : lratChecker f8822 p8822 = .success := by decide +kernel
theorem unsat8822 : Unsatisfiable (PosFin 65) f8822 := by
  apply lratCheckerSound f8822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8822
  · intro a ha; simp [p8822] at ha; subst a; trivial
  · exact checked8822
theorem derived8822 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8822 := by
  apply localUnsat_implies_entails f8822 [c8804, c8686, c8421, c8814, c8816, c8819, c8821, c8715, c8812] c8822 unsat8822 (by rfl) a
  have h0 : Entails.eval a c8804 := derived8804 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8814 := derived8814 a h
  have h4 : Entails.eval a c8816 := derived8816 a h
  have h5 : Entails.eval a c8819 := derived8819 a h
  have h6 : Entails.eval a c8821 := derived8821 a h
  have h7 : Entails.eval a c8715 := derived8715 a h
  have h8 : Entails.eval a c8812 := derived8812 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8823 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8823 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6068, some c6248, some c5844, some c5843, some c5848, some c5850, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8823 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8823 : lratChecker f8823 p8823 = .success := by decide +kernel
theorem unsat8823 : Unsatisfiable (PosFin 65) f8823 := by
  apply lratCheckerSound f8823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8823
  · intro a ha; simp [p8823] at ha; subst a; trivial
  · exact checked8823
theorem derived8823 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8823 := by
  apply localUnsat_implies_entails f8823 [c8269, c6068, c6248, c5844, c5843, c5848, c5850] c8823 unsat8823 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6068 := h 6067 (by decide)
  have h2 : Entails.eval a c6248 := h 6247 (by decide)
  have h3 : Entails.eval a c5844 := h 5843 (by decide)
  have h4 : Entails.eval a c5843 := h 5842 (by decide)
  have h5 : Entails.eval a c5848 := h 5847 (by decide)
  have h6 : Entails.eval a c5850 := h 5849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8824 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8824 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8823, some c645, some c636, some c620, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8824 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8824 : lratChecker f8824 p8824 = .success := by decide +kernel
theorem unsat8824 : Unsatisfiable (PosFin 65) f8824 := by
  apply lratCheckerSound f8824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8824
  · intro a ha; simp [p8824] at ha; subst a; trivial
  · exact checked8824
theorem derived8824 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8824 := by
  apply localUnsat_implies_entails f8824 [c8823, c645, c636, c620] c8824 unsat8824 (by rfl) a
  have h0 : Entails.eval a c8823 := derived8823 a h
  have h1 : Entails.eval a c645 := h 644 (by decide)
  have h2 : Entails.eval a c636 := h 635 (by decide)
  have h3 : Entails.eval a c620 := h 619 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8825 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8825 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8713, some c8714, some c6123, some c6090, some c6205, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8825 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8825 : lratChecker f8825 p8825 = .success := by decide +kernel
theorem unsat8825 : Unsatisfiable (PosFin 65) f8825 := by
  apply lratCheckerSound f8825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8825
  · intro a ha; simp [p8825] at ha; subst a; trivial
  · exact checked8825
theorem derived8825 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8825 := by
  apply localUnsat_implies_entails f8825 [c8713, c8714, c6123, c6090, c6205] c8825 unsat8825 (by rfl) a
  have h0 : Entails.eval a c8713 := derived8713 a h
  have h1 : Entails.eval a c8714 := derived8714 a h
  have h2 : Entails.eval a c6123 := h 6122 (by decide)
  have h3 : Entails.eval a c6090 := h 6089 (by decide)
  have h4 : Entails.eval a c6205 := h 6204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8826 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨1, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8826 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c631, some c627, some c620, some c634, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8826 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8826 : lratChecker f8826 p8826 = .success := by decide +kernel
theorem unsat8826 : Unsatisfiable (PosFin 65) f8826 := by
  apply lratCheckerSound f8826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8826
  · intro a ha; simp [p8826] at ha; subst a; trivial
  · exact checked8826
theorem derived8826 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8826 := by
  apply localUnsat_implies_entails f8826 [c631, c627, c620, c634] c8826 unsat8826 (by rfl) a
  have h0 : Entails.eval a c631 := h 630 (by decide)
  have h1 : Entails.eval a c627 := h 626 (by decide)
  have h2 : Entails.eval a c620 := h 619 (by decide)
  have h3 : Entails.eval a c634 := h 633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8827 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8827 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8824, some c8825, some c8812, some c8826, some c616, some c639, some c638, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8827 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8827 : lratChecker f8827 p8827 = .success := by decide +kernel
theorem unsat8827 : Unsatisfiable (PosFin 65) f8827 := by
  apply lratCheckerSound f8827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8827
  · intro a ha; simp [p8827] at ha; subst a; trivial
  · exact checked8827
theorem derived8827 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8827 := by
  apply localUnsat_implies_entails f8827 [c8824, c8825, c8812, c8826, c616, c639, c638] c8827 unsat8827 (by rfl) a
  have h0 : Entails.eval a c8824 := derived8824 a h
  have h1 : Entails.eval a c8825 := derived8825 a h
  have h2 : Entails.eval a c8812 := derived8812 a h
  have h3 : Entails.eval a c8826 := derived8826 a h
  have h4 : Entails.eval a c616 := h 615 (by decide)
  have h5 : Entails.eval a c639 := h 638 (by decide)
  have h6 : Entails.eval a c638 := h 637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8828 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8828 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5819, some c8743, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8828 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8828 : lratChecker f8828 p8828 = .success := by decide +kernel
theorem unsat8828 : Unsatisfiable (PosFin 65) f8828 := by
  apply lratCheckerSound f8828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8828
  · intro a ha; simp [p8828] at ha; subst a; trivial
  · exact checked8828
theorem derived8828 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8828 := by
  apply localUnsat_implies_entails f8828 [c5819, c8743] c8828 unsat8828 (by rfl) a
  have h0 : Entails.eval a c5819 := h 5818 (by decide)
  have h1 : Entails.eval a c8743 := derived8743 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8829 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8829 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8719, some c5820, some c8799, some c5829, some c5827, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8829 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8829 : lratChecker f8829 p8829 = .success := by decide +kernel
theorem unsat8829 : Unsatisfiable (PosFin 65) f8829 := by
  apply lratCheckerSound f8829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8829
  · intro a ha; simp [p8829] at ha; subst a; trivial
  · exact checked8829
theorem derived8829 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8829 := by
  apply localUnsat_implies_entails f8829 [c8719, c5820, c8799, c5829, c5827] c8829 unsat8829 (by rfl) a
  have h0 : Entails.eval a c8719 := derived8719 a h
  have h1 : Entails.eval a c5820 := h 5819 (by decide)
  have h2 : Entails.eval a c8799 := derived8799 a h
  have h3 : Entails.eval a c5829 := h 5828 (by decide)
  have h4 : Entails.eval a c5827 := h 5826 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8830 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨27, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8830 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8822, some c8804, some c8827, some c8828, some c8421, some c5474, some c193, some c5447, some c1, some c4901, some c6150, some c8829, some c8791, some c145, some c2770, some c2722, some c5306, some c4494, some c4248, some c4724, some c122, some c154, some c77, some c349, some c6125, some c390, some c5685, some c5293, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8830 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked8830 : lratChecker f8830 p8830 = .success := by decide +kernel
theorem unsat8830 : Unsatisfiable (PosFin 65) f8830 := by
  apply lratCheckerSound f8830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8830
  · intro a ha; simp [p8830] at ha; subst a; trivial
  · exact checked8830
theorem derived8830 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8830 := by
  apply localUnsat_implies_entails f8830 [c8686, c8822, c8804, c8827, c8828, c8421, c5474, c193, c5447, c1, c4901, c6150, c8829, c8791, c145, c2770, c2722, c5306, c4494, c4248, c4724, c122, c154, c77, c349, c6125, c390, c5685, c5293] c8830 unsat8830 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8822 := derived8822 a h
  have h2 : Entails.eval a c8804 := derived8804 a h
  have h3 : Entails.eval a c8827 := derived8827 a h
  have h4 : Entails.eval a c8828 := derived8828 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c5474 := h 5473 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c5447 := h 5446 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c4901 := h 4900 (by decide)
  have h11 : Entails.eval a c6150 := h 6149 (by decide)
  have h12 : Entails.eval a c8829 := derived8829 a h
  have h13 : Entails.eval a c8791 := derived8791 a h
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c2770 := h 2769 (by decide)
  have h16 : Entails.eval a c2722 := h 2721 (by decide)
  have h17 : Entails.eval a c5306 := h 5305 (by decide)
  have h18 : Entails.eval a c4494 := h 4493 (by decide)
  have h19 : Entails.eval a c4248 := h 4247 (by decide)
  have h20 : Entails.eval a c4724 := h 4723 (by decide)
  have h21 : Entails.eval a c122 := h 121 (by decide)
  have h22 : Entails.eval a c154 := h 153 (by decide)
  have h23 : Entails.eval a c77 := h 76 (by decide)
  have h24 : Entails.eval a c349 := h 348 (by decide)
  have h25 : Entails.eval a c6125 := h 6124 (by decide)
  have h26 : Entails.eval a c390 := h 389 (by decide)
  have h27 : Entails.eval a c5685 := h 5684 (by decide)
  have h28 : Entails.eval a c5293 := h 5292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8831 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8831 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1412, some c8829, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8831 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8831 : lratChecker f8831 p8831 = .success := by decide +kernel
theorem unsat8831 : Unsatisfiable (PosFin 65) f8831 := by
  apply lratCheckerSound f8831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8831
  · intro a ha; simp [p8831] at ha; subst a; trivial
  · exact checked8831
theorem derived8831 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8831 := by
  apply localUnsat_implies_entails f8831 [c1412, c8829] c8831 unsat8831 (by rfl) a
  have h0 : Entails.eval a c1412 := h 1411 (by decide)
  have h1 : Entails.eval a c8829 := derived8829 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8832 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8832 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8686, some c8822, some c8804, some c8827, some c8828, some c8831, some c8830, some c8826, some c1127, some c1073, some c373, some c5799, some c4597, some c1428, some c5801, some c4909, some c5800, some c5485, some c2782, some c8472, some c5307, some c154, some c851, some c127, some c4248, some c5916, some c403, some c854, some c60, some c5804, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8832 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked8832 : lratChecker f8832 p8832 = .success := by decide +kernel
theorem unsat8832 : Unsatisfiable (PosFin 65) f8832 := by
  apply lratCheckerSound f8832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8832
  · intro a ha; simp [p8832] at ha; subst a; trivial
  · exact checked8832
theorem derived8832 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8832 := by
  apply localUnsat_implies_entails f8832 [c8421, c8686, c8822, c8804, c8827, c8828, c8831, c8830, c8826, c1127, c1073, c373, c5799, c4597, c1428, c5801, c4909, c5800, c5485, c2782, c8472, c5307, c154, c851, c127, c4248, c5916, c403, c854, c60, c5804] c8832 unsat8832 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8822 := derived8822 a h
  have h3 : Entails.eval a c8804 := derived8804 a h
  have h4 : Entails.eval a c8827 := derived8827 a h
  have h5 : Entails.eval a c8828 := derived8828 a h
  have h6 : Entails.eval a c8831 := derived8831 a h
  have h7 : Entails.eval a c8830 := derived8830 a h
  have h8 : Entails.eval a c8826 := derived8826 a h
  have h9 : Entails.eval a c1127 := h 1126 (by decide)
  have h10 : Entails.eval a c1073 := h 1072 (by decide)
  have h11 : Entails.eval a c373 := h 372 (by decide)
  have h12 : Entails.eval a c5799 := h 5798 (by decide)
  have h13 : Entails.eval a c4597 := h 4596 (by decide)
  have h14 : Entails.eval a c1428 := h 1427 (by decide)
  have h15 : Entails.eval a c5801 := h 5800 (by decide)
  have h16 : Entails.eval a c4909 := h 4908 (by decide)
  have h17 : Entails.eval a c5800 := h 5799 (by decide)
  have h18 : Entails.eval a c5485 := h 5484 (by decide)
  have h19 : Entails.eval a c2782 := h 2781 (by decide)
  have h20 : Entails.eval a c8472 := derived8472 a h
  have h21 : Entails.eval a c5307 := h 5306 (by decide)
  have h22 : Entails.eval a c154 := h 153 (by decide)
  have h23 : Entails.eval a c851 := h 850 (by decide)
  have h24 : Entails.eval a c127 := h 126 (by decide)
  have h25 : Entails.eval a c4248 := h 4247 (by decide)
  have h26 : Entails.eval a c5916 := h 5915 (by decide)
  have h27 : Entails.eval a c403 := h 402 (by decide)
  have h28 : Entails.eval a c854 := h 853 (by decide)
  have h29 : Entails.eval a c60 := h 59 (by decide)
  have h30 : Entails.eval a c5804 := h 5803 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8833 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8833 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8828, some c5474, some c8791, some c145, some c160, some c122, some c5666, some c5640, some c5685, some c6156, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8833 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8833 : lratChecker f8833 p8833 = .success := by decide +kernel
theorem unsat8833 : Unsatisfiable (PosFin 65) f8833 := by
  apply lratCheckerSound f8833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8833
  · intro a ha; simp [p8833] at ha; subst a; trivial
  · exact checked8833
theorem derived8833 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8833 := by
  apply localUnsat_implies_entails f8833 [c8828, c5474, c8791, c145, c160, c122, c5666, c5640, c5685, c6156] c8833 unsat8833 (by rfl) a
  have h0 : Entails.eval a c8828 := derived8828 a h
  have h1 : Entails.eval a c5474 := h 5473 (by decide)
  have h2 : Entails.eval a c8791 := derived8791 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c5666 := h 5665 (by decide)
  have h7 : Entails.eval a c5640 := h 5639 (by decide)
  have h8 : Entails.eval a c5685 := h 5684 (by decide)
  have h9 : Entails.eval a c6156 := h 6155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8834 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8834 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8804, some c8686, some c8421, some c8822, some c8827, some c8828, some c8831, some c8832, some c8833, some c8812, some c8826, some c616, some c608, some c638, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8834 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8834 : lratChecker f8834 p8834 = .success := by decide +kernel
theorem unsat8834 : Unsatisfiable (PosFin 65) f8834 := by
  apply lratCheckerSound f8834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8834
  · intro a ha; simp [p8834] at ha; subst a; trivial
  · exact checked8834
theorem derived8834 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8834 := by
  apply localUnsat_implies_entails f8834 [c8804, c8686, c8421, c8822, c8827, c8828, c8831, c8832, c8833, c8812, c8826, c616, c608, c638] c8834 unsat8834 (by rfl) a
  have h0 : Entails.eval a c8804 := derived8804 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8822 := derived8822 a h
  have h4 : Entails.eval a c8827 := derived8827 a h
  have h5 : Entails.eval a c8828 := derived8828 a h
  have h6 : Entails.eval a c8831 := derived8831 a h
  have h7 : Entails.eval a c8832 := derived8832 a h
  have h8 : Entails.eval a c8833 := derived8833 a h
  have h9 : Entails.eval a c8812 := derived8812 a h
  have h10 : Entails.eval a c8826 := derived8826 a h
  have h11 : Entails.eval a c616 := h 615 (by decide)
  have h12 : Entails.eval a c608 := h 607 (by decide)
  have h13 : Entails.eval a c638 := h 637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8835 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8835 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c600, some c596, some c577, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8835 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8835 : lratChecker f8835 p8835 = .success := by decide +kernel
theorem unsat8835 : Unsatisfiable (PosFin 65) f8835 := by
  apply lratCheckerSound f8835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8835
  · intro a ha; simp [p8835] at ha; subst a; trivial
  · exact checked8835
theorem derived8835 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8835 := by
  apply localUnsat_implies_entails f8835 [c600, c596, c577] c8835 unsat8835 (by rfl) a
  have h0 : Entails.eval a c600 := h 599 (by decide)
  have h1 : Entails.eval a c596 := h 595 (by decide)
  have h2 : Entails.eval a c577 := h 576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8836 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8836 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c560, some c559, some c597, some c588, some c581, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8836 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8836 : lratChecker f8836 p8836 = .success := by decide +kernel
theorem unsat8836 : Unsatisfiable (PosFin 65) f8836 := by
  apply lratCheckerSound f8836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8836
  · intro a ha; simp [p8836] at ha; subst a; trivial
  · exact checked8836
theorem derived8836 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8836 := by
  apply localUnsat_implies_entails f8836 [c560, c559, c597, c588, c581] c8836 unsat8836 (by rfl) a
  have h0 : Entails.eval a c560 := h 559 (by decide)
  have h1 : Entails.eval a c559 := h 558 (by decide)
  have h2 : Entails.eval a c597 := h 596 (by decide)
  have h3 : Entails.eval a c588 := h 587 (by decide)
  have h4 : Entails.eval a c581 := h 580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8837 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8837 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c577, some c581, some c597, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8837 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8837 : lratChecker f8837 p8837 = .success := by decide +kernel
theorem unsat8837 : Unsatisfiable (PosFin 65) f8837 := by
  apply lratCheckerSound f8837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8837
  · intro a ha; simp [p8837] at ha; subst a; trivial
  · exact checked8837
theorem derived8837 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8837 := by
  apply localUnsat_implies_entails f8837 [c577, c581, c597] c8837 unsat8837 (by rfl) a
  have h0 : Entails.eval a c577 := h 576 (by decide)
  have h1 : Entails.eval a c581 := h 580 (by decide)
  have h2 : Entails.eval a c597 := h 596 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8838 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8838 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8835, some c8836, some c8837, some c564, some c568, some c591, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8838 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8838 : lratChecker f8838 p8838 = .success := by decide +kernel
theorem unsat8838 : Unsatisfiable (PosFin 65) f8838 := by
  apply lratCheckerSound f8838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8838
  · intro a ha; simp [p8838] at ha; subst a; trivial
  · exact checked8838
theorem derived8838 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8838 := by
  apply localUnsat_implies_entails f8838 [c8835, c8836, c8837, c564, c568, c591] c8838 unsat8838 (by rfl) a
  have h0 : Entails.eval a c8835 := derived8835 a h
  have h1 : Entails.eval a c8836 := derived8836 a h
  have h2 : Entails.eval a c8837 := derived8837 a h
  have h3 : Entails.eval a c564 := h 563 (by decide)
  have h4 : Entails.eval a c568 := h 567 (by decide)
  have h5 : Entails.eval a c591 := h 590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8839 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8839 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c599, some c584, some c570, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8839 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8839 : lratChecker f8839 p8839 = .success := by decide +kernel
theorem unsat8839 : Unsatisfiable (PosFin 65) f8839 := by
  apply lratCheckerSound f8839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8839
  · intro a ha; simp [p8839] at ha; subst a; trivial
  · exact checked8839
theorem derived8839 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8839 := by
  apply localUnsat_implies_entails f8839 [c599, c584, c570] c8839 unsat8839 (by rfl) a
  have h0 : Entails.eval a c599 := h 598 (by decide)
  have h1 : Entails.eval a c584 := h 583 (by decide)
  have h2 : Entails.eval a c570 := h 569 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8840 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8840 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c577, some c581, some c570, some c582, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8840 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8840 : lratChecker f8840 p8840 = .success := by decide +kernel
theorem unsat8840 : Unsatisfiable (PosFin 65) f8840 := by
  apply lratCheckerSound f8840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8840
  · intro a ha; simp [p8840] at ha; subst a; trivial
  · exact checked8840
theorem derived8840 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8840 := by
  apply localUnsat_implies_entails f8840 [c577, c581, c570, c582] c8840 unsat8840 (by rfl) a
  have h0 : Entails.eval a c577 := h 576 (by decide)
  have h1 : Entails.eval a c581 := h 580 (by decide)
  have h2 : Entails.eval a c570 := h 569 (by decide)
  have h3 : Entails.eval a c582 := h 581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8841 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8841 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8838, some c8731, some c8839, some c564, some c568, some c591, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8841 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8841 : lratChecker f8841 p8841 = .success := by decide +kernel
theorem unsat8841 : Unsatisfiable (PosFin 65) f8841 := by
  apply lratCheckerSound f8841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8841
  · intro a ha; simp [p8841] at ha; subst a; trivial
  · exact checked8841
theorem derived8841 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8841 := by
  apply localUnsat_implies_entails f8841 [c8840, c8838, c8731, c8839, c564, c568, c591] c8841 unsat8841 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8838 := derived8838 a h
  have h2 : Entails.eval a c8731 := derived8731 a h
  have h3 : Entails.eval a c8839 := derived8839 a h
  have h4 : Entails.eval a c564 := h 563 (by decide)
  have h5 : Entails.eval a c568 := h 567 (by decide)
  have h6 : Entails.eval a c591 := h 590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8842 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨53, by decide⟩, true), (⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8842 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5686, some c8690, some c7994, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8842 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8842 : lratChecker f8842 p8842 = .success := by decide +kernel
theorem unsat8842 : Unsatisfiable (PosFin 65) f8842 := by
  apply lratCheckerSound f8842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8842
  · intro a ha; simp [p8842] at ha; subst a; trivial
  · exact checked8842
theorem derived8842 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8842 := by
  apply localUnsat_implies_entails f8842 [c5686, c8690, c7994] c8842 unsat8842 (by rfl) a
  have h0 : Entails.eval a c5686 := h 5685 (by decide)
  have h1 : Entails.eval a c8690 := derived8690 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8843 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨22, by decide⟩, false), (⟨30, by decide⟩, true), (⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨31, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8843 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8842, some c5656, some c726, some c1408, some c372, some c5614, some c4432, some c62, some c5680, some c8715, some c5654, some c4863, some c84, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8843 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8843 : lratChecker f8843 p8843 = .success := by decide +kernel
theorem unsat8843 : Unsatisfiable (PosFin 65) f8843 := by
  apply lratCheckerSound f8843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8843
  · intro a ha; simp [p8843] at ha; subst a; trivial
  · exact checked8843
theorem derived8843 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8843 := by
  apply localUnsat_implies_entails f8843 [c8842, c5656, c726, c1408, c372, c5614, c4432, c62, c5680, c8715, c5654, c4863, c84] c8843 unsat8843 (by rfl) a
  have h0 : Entails.eval a c8842 := derived8842 a h
  have h1 : Entails.eval a c5656 := h 5655 (by decide)
  have h2 : Entails.eval a c726 := h 725 (by decide)
  have h3 : Entails.eval a c1408 := h 1407 (by decide)
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c5614 := h 5613 (by decide)
  have h6 : Entails.eval a c4432 := h 4431 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c5680 := h 5679 (by decide)
  have h9 : Entails.eval a c8715 := derived8715 a h
  have h10 : Entails.eval a c5654 := h 5653 (by decide)
  have h11 : Entails.eval a c4863 := h 4862 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8844 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨31, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8844 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8708, some c5654, some c5621, some c5694, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8844 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8844 : lratChecker f8844 p8844 = .success := by decide +kernel
theorem unsat8844 : Unsatisfiable (PosFin 65) f8844 := by
  apply lratCheckerSound f8844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8844
  · intro a ha; simp [p8844] at ha; subst a; trivial
  · exact checked8844
theorem derived8844 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8844 := by
  apply localUnsat_implies_entails f8844 [c8708, c5654, c5621, c5694] c8844 unsat8844 (by rfl) a
  have h0 : Entails.eval a c8708 := derived8708 a h
  have h1 : Entails.eval a c5654 := h 5653 (by decide)
  have h2 : Entails.eval a c5621 := h 5620 (by decide)
  have h3 : Entails.eval a c5694 := h 5693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8845 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8845 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8804, some c8834, some c8841, some c8840, some c8686, some c8421, some c8835, some c593, some c590, some c591, some c589, some c597, some c572, some c586, some c8843, some c8844, some c8715, some c8812, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8845 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8845 : lratChecker f8845 p8845 = .success := by decide +kernel
theorem unsat8845 : Unsatisfiable (PosFin 65) f8845 := by
  apply lratCheckerSound f8845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8845
  · intro a ha; simp [p8845] at ha; subst a; trivial
  · exact checked8845
theorem derived8845 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8845 := by
  apply localUnsat_implies_entails f8845 [c8804, c8834, c8841, c8840, c8686, c8421, c8835, c593, c590, c591, c589, c597, c572, c586, c8843, c8844, c8715, c8812] c8845 unsat8845 (by rfl) a
  have h0 : Entails.eval a c8804 := derived8804 a h
  have h1 : Entails.eval a c8834 := derived8834 a h
  have h2 : Entails.eval a c8841 := derived8841 a h
  have h3 : Entails.eval a c8840 := derived8840 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8835 := derived8835 a h
  have h7 : Entails.eval a c593 := h 592 (by decide)
  have h8 : Entails.eval a c590 := h 589 (by decide)
  have h9 : Entails.eval a c591 := h 590 (by decide)
  have h10 : Entails.eval a c589 := h 588 (by decide)
  have h11 : Entails.eval a c597 := h 596 (by decide)
  have h12 : Entails.eval a c572 := h 571 (by decide)
  have h13 : Entails.eval a c586 := h 585 (by decide)
  have h14 : Entails.eval a c8843 := derived8843 a h
  have h15 : Entails.eval a c8844 := derived8844 a h
  have h16 : Entails.eval a c8715 := derived8715 a h
  have h17 : Entails.eval a c8812 := derived8812 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8846 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨50, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8846 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c564, some c566, some c568, some c591, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p8846 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8846 : lratChecker f8846 p8846 = .success := by decide +kernel
theorem unsat8846 : Unsatisfiable (PosFin 65) f8846 := by
  apply lratCheckerSound f8846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8846
  · intro a ha; simp [p8846] at ha; subst a; trivial
  · exact checked8846
theorem derived8846 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8846 := by
  apply localUnsat_implies_entails f8846 [c564, c566, c568, c591] c8846 unsat8846 (by rfl) a
  have h0 : Entails.eval a c564 := h 563 (by decide)
  have h1 : Entails.eval a c566 := h 565 (by decide)
  have h2 : Entails.eval a c568 := h 567 (by decide)
  have h3 : Entails.eval a c591 := h 590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8847 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8847 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8804, some c8834, some c8840, some c8845, some c8731, some c8846, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8847 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8847 : lratChecker f8847 p8847 = .success := by decide +kernel
theorem unsat8847 : Unsatisfiable (PosFin 65) f8847 := by
  apply lratCheckerSound f8847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8847
  · intro a ha; simp [p8847] at ha; subst a; trivial
  · exact checked8847
theorem derived8847 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8847 := by
  apply localUnsat_implies_entails f8847 [c8804, c8834, c8840, c8845, c8731, c8846] c8847 unsat8847 (by rfl) a
  have h0 : Entails.eval a c8804 := derived8804 a h
  have h1 : Entails.eval a c8834 := derived8834 a h
  have h2 : Entails.eval a c8840 := derived8840 a h
  have h3 : Entails.eval a c8845 := derived8845 a h
  have h4 : Entails.eval a c8731 := derived8731 a h
  have h5 : Entails.eval a c8846 := derived8846 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8848 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8848 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5967, some c5969, some c8590, some c5971, some c5970, some c6003, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8848 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8848 : lratChecker f8848 p8848 = .success := by decide +kernel
theorem unsat8848 : Unsatisfiable (PosFin 65) f8848 := by
  apply lratCheckerSound f8848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8848
  · intro a ha; simp [p8848] at ha; subst a; trivial
  · exact checked8848
theorem derived8848 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8848 := by
  apply localUnsat_implies_entails f8848 [c5967, c5969, c8590, c5971, c5970, c6003] c8848 unsat8848 (by rfl) a
  have h0 : Entails.eval a c5967 := h 5966 (by decide)
  have h1 : Entails.eval a c5969 := h 5968 (by decide)
  have h2 : Entails.eval a c8590 := derived8590 a h
  have h3 : Entails.eval a c5971 := h 5970 (by decide)
  have h4 : Entails.eval a c5970 := h 5969 (by decide)
  have h5 : Entails.eval a c6003 := h 6002 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8849 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8849 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5944, some c5888, some c6192, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8849 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8849 : lratChecker f8849 p8849 = .success := by decide +kernel
theorem unsat8849 : Unsatisfiable (PosFin 65) f8849 := by
  apply lratCheckerSound f8849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8849
  · intro a ha; simp [p8849] at ha; subst a; trivial
  · exact checked8849
theorem derived8849 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8849 := by
  apply localUnsat_implies_entails f8849 [c5944, c5888, c6192] c8849 unsat8849 (by rfl) a
  have h0 : Entails.eval a c5944 := h 5943 (by decide)
  have h1 : Entails.eval a c5888 := h 5887 (by decide)
  have h2 : Entails.eval a c6192 := h 6191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8850 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8850 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8269, some c8848, some c8849, some c8686, some c8724, some c8421, some c1191, some c1129, some c4438, some c5884, some c832, some c2639, some c4188, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8850 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8850 : lratChecker f8850 p8850 = .success := by decide +kernel
theorem unsat8850 : Unsatisfiable (PosFin 65) f8850 := by
  apply lratCheckerSound f8850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8850
  · intro a ha; simp [p8850] at ha; subst a; trivial
  · exact checked8850
theorem derived8850 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8850 := by
  apply localUnsat_implies_entails f8850 [c8847, c8269, c8848, c8849, c8686, c8724, c8421, c1191, c1129, c4438, c5884, c832, c2639, c4188] c8850 unsat8850 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8848 := derived8848 a h
  have h3 : Entails.eval a c8849 := derived8849 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8724 := derived8724 a h
  have h6 : Entails.eval a c8421 := derived8421 a h
  have h7 : Entails.eval a c1191 := h 1190 (by decide)
  have h8 : Entails.eval a c1129 := h 1128 (by decide)
  have h9 : Entails.eval a c4438 := h 4437 (by decide)
  have h10 : Entails.eval a c5884 := h 5883 (by decide)
  have h11 : Entails.eval a c832 := h 831 (by decide)
  have h12 : Entails.eval a c2639 := h 2638 (by decide)
  have h13 : Entails.eval a c4188 := h 4187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8850

end CochromaticTwenty.Certificates.FixedCore0
