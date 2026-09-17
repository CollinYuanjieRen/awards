import MerLeanExperiment.Certificates.FixedCore0.Steps0000_0099

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7651 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7651 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5192, some c5142, some c5182, some c5338, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7651 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7651 : lratChecker f7651 p7651 = .success := by decide +kernel
theorem unsat7651 : Unsatisfiable (PosFin 65) f7651 := by
  apply lratCheckerSound f7651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7651
  · intro a ha; simp [p7651] at ha; subst a; trivial
  · exact checked7651
theorem derived7651 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7651 := by
  apply localUnsat_implies_entails f7651 [c5192, c5142, c5182, c5338] c7651 unsat7651 (by rfl) a
  have h0 : Entails.eval a c5192 := h 5191 (by decide)
  have h1 : Entails.eval a c5142 := h 5141 (by decide)
  have h2 : Entails.eval a c5182 := h 5181 (by decide)
  have h3 : Entails.eval a c5338 := h 5337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7652 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7652 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5214, some c5157, some c5226, some c5421, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7652 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7652 : lratChecker f7652 p7652 = .success := by decide +kernel
theorem unsat7652 : Unsatisfiable (PosFin 65) f7652 := by
  apply lratCheckerSound f7652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7652
  · intro a ha; simp [p7652] at ha; subst a; trivial
  · exact checked7652
theorem derived7652 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7652 := by
  apply localUnsat_implies_entails f7652 [c5214, c5157, c5226, c5421] c7652 unsat7652 (by rfl) a
  have h0 : Entails.eval a c5214 := h 5213 (by decide)
  have h1 : Entails.eval a c5157 := h 5156 (by decide)
  have h2 : Entails.eval a c5226 := h 5225 (by decide)
  have h3 : Entails.eval a c5421 := h 5420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7653 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7653 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7642, some c6853, some c6864, some c7079, some c6335, some c7033, some c7220, some c6752, some c7637, some c7650, some c7319, some c7651, some c7652, some c7649, some c5534, some c5717, some c5167, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7653 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7653 : lratChecker f7653 p7653 = .success := by decide +kernel
theorem unsat7653 : Unsatisfiable (PosFin 65) f7653 := by
  apply lratCheckerSound f7653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7653
  · intro a ha; simp [p7653] at ha; subst a; trivial
  · exact checked7653
theorem derived7653 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7653 := by
  apply localUnsat_implies_entails f7653 [c7642, c6853, c6864, c7079, c6335, c7033, c7220, c6752, c7637, c7650, c7319, c7651, c7652, c7649, c5534, c5717, c5167] c7653 unsat7653 (by rfl) a
  have h0 : Entails.eval a c7642 := derived7642 a h
  have h1 : Entails.eval a c6853 := h 6852 (by decide)
  have h2 : Entails.eval a c6864 := h 6863 (by decide)
  have h3 : Entails.eval a c7079 := h 7078 (by decide)
  have h4 : Entails.eval a c6335 := h 6334 (by decide)
  have h5 : Entails.eval a c7033 := h 7032 (by decide)
  have h6 : Entails.eval a c7220 := h 7219 (by decide)
  have h7 : Entails.eval a c6752 := h 6751 (by decide)
  have h8 : Entails.eval a c7637 := derived7637 a h
  have h9 : Entails.eval a c7650 := derived7650 a h
  have h10 : Entails.eval a c7319 := h 7318 (by decide)
  have h11 : Entails.eval a c7651 := derived7651 a h
  have h12 : Entails.eval a c7652 := derived7652 a h
  have h13 : Entails.eval a c7649 := derived7649 a h
  have h14 : Entails.eval a c5534 := h 5533 (by decide)
  have h15 : Entails.eval a c5717 := h 5716 (by decide)
  have h16 : Entails.eval a c5167 := h 5166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7654 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7654 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7653, some c6925, some c6787, some c6335, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7654 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7654 : lratChecker f7654 p7654 = .success := by decide +kernel
theorem unsat7654 : Unsatisfiable (PosFin 65) f7654 := by
  apply lratCheckerSound f7654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7654
  · intro a ha; simp [p7654] at ha; subst a; trivial
  · exact checked7654
theorem derived7654 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7654 := by
  apply localUnsat_implies_entails f7654 [c7653, c6925, c6787, c6335] c7654 unsat7654 (by rfl) a
  have h0 : Entails.eval a c7653 := derived7653 a h
  have h1 : Entails.eval a c6925 := h 6924 (by decide)
  have h2 : Entails.eval a c6787 := h 6786 (by decide)
  have h3 : Entails.eval a c6335 := h 6334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7655 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨55, by decide⟩, true), (⟨54, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7655 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5526, some c5737, some c5712, some c5617, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7655 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7655 : lratChecker f7655 p7655 = .success := by decide +kernel
theorem unsat7655 : Unsatisfiable (PosFin 65) f7655 := by
  apply lratCheckerSound f7655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7655
  · intro a ha; simp [p7655] at ha; subst a; trivial
  · exact checked7655
theorem derived7655 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7655 := by
  apply localUnsat_implies_entails f7655 [c5526, c5737, c5712, c5617] c7655 unsat7655 (by rfl) a
  have h0 : Entails.eval a c5526 := h 5525 (by decide)
  have h1 : Entails.eval a c5737 := h 5736 (by decide)
  have h2 : Entails.eval a c5712 := h 5711 (by decide)
  have h3 : Entails.eval a c5617 := h 5616 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7656 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨55, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨54, by decide⟩, false), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7656 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5144, some c5183, some c5193, some c5339, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7656 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7656 : lratChecker f7656 p7656 = .success := by decide +kernel
theorem unsat7656 : Unsatisfiable (PosFin 65) f7656 := by
  apply lratCheckerSound f7656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7656
  · intro a ha; simp [p7656] at ha; subst a; trivial
  · exact checked7656
theorem derived7656 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7656 := by
  apply localUnsat_implies_entails f7656 [c5144, c5183, c5193, c5339] c7656 unsat7656 (by rfl) a
  have h0 : Entails.eval a c5144 := h 5143 (by decide)
  have h1 : Entails.eval a c5183 := h 5182 (by decide)
  have h2 : Entails.eval a c5193 := h 5192 (by decide)
  have h3 : Entails.eval a c5339 := h 5338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7657 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨54, by decide⟩, false), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7657 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7656, some c7655, some c5159, some c5227, some c5215, some c5422, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7657 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7657 : lratChecker f7657 p7657 = .success := by decide +kernel
theorem unsat7657 : Unsatisfiable (PosFin 65) f7657 := by
  apply lratCheckerSound f7657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7657
  · intro a ha; simp [p7657] at ha; subst a; trivial
  · exact checked7657
theorem derived7657 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7657 := by
  apply localUnsat_implies_entails f7657 [c7656, c7655, c5159, c5227, c5215, c5422] c7657 unsat7657 (by rfl) a
  have h0 : Entails.eval a c7656 := derived7656 a h
  have h1 : Entails.eval a c7655 := derived7655 a h
  have h2 : Entails.eval a c5159 := h 5158 (by decide)
  have h3 : Entails.eval a c5227 := h 5226 (by decide)
  have h4 : Entails.eval a c5215 := h 5214 (by decide)
  have h5 : Entails.eval a c5422 := h 5421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7658 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨54, by decide⟩, false), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7658 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5160, some c5228, some c5215, some c5422, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7658 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7658 : lratChecker f7658 p7658 = .success := by decide +kernel
theorem unsat7658 : Unsatisfiable (PosFin 65) f7658 := by
  apply lratCheckerSound f7658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7658
  · intro a ha; simp [p7658] at ha; subst a; trivial
  · exact checked7658
theorem derived7658 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7658 := by
  apply localUnsat_implies_entails f7658 [c5160, c5228, c5215, c5422] c7658 unsat7658 (by rfl) a
  have h0 : Entails.eval a c5160 := h 5159 (by decide)
  have h1 : Entails.eval a c5228 := h 5227 (by decide)
  have h2 : Entails.eval a c5215 := h 5214 (by decide)
  have h3 : Entails.eval a c5422 := h 5421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7659 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨54, by decide⟩, false), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7659 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7636, some c6336, some c7467, some c7237, some c6926, some c6721, some c7183, some c7657, some c7333, some c7658, some c7649, some c5145, some c5184, some c5193, some c5339, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7659 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7659 : lratChecker f7659 p7659 = .success := by decide +kernel
theorem unsat7659 : Unsatisfiable (PosFin 65) f7659 := by
  apply lratCheckerSound f7659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7659
  · intro a ha; simp [p7659] at ha; subst a; trivial
  · exact checked7659
theorem derived7659 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7659 := by
  apply localUnsat_implies_entails f7659 [c7636, c6336, c7467, c7237, c6926, c6721, c7183, c7657, c7333, c7658, c7649, c5145, c5184, c5193, c5339] c7659 unsat7659 (by rfl) a
  have h0 : Entails.eval a c7636 := derived7636 a h
  have h1 : Entails.eval a c6336 := h 6335 (by decide)
  have h2 : Entails.eval a c7467 := h 7466 (by decide)
  have h3 : Entails.eval a c7237 := h 7236 (by decide)
  have h4 : Entails.eval a c6926 := h 6925 (by decide)
  have h5 : Entails.eval a c6721 := h 6720 (by decide)
  have h6 : Entails.eval a c7183 := h 7182 (by decide)
  have h7 : Entails.eval a c7657 := derived7657 a h
  have h8 : Entails.eval a c7333 := h 7332 (by decide)
  have h9 : Entails.eval a c7658 := derived7658 a h
  have h10 : Entails.eval a c7649 := derived7649 a h
  have h11 : Entails.eval a c5145 := h 5144 (by decide)
  have h12 : Entails.eval a c5184 := h 5183 (by decide)
  have h13 : Entails.eval a c5193 := h 5192 (by decide)
  have h14 : Entails.eval a c5339 := h 5338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7660 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7660 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7641, some c7636, some c7654, some c7659, some c7606, some c6788, some c6323, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7660 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7660 : lratChecker f7660 p7660 = .success := by decide +kernel
theorem unsat7660 : Unsatisfiable (PosFin 65) f7660 := by
  apply lratCheckerSound f7660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7660
  · intro a ha; simp [p7660] at ha; subst a; trivial
  · exact checked7660
theorem derived7660 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7660 := by
  apply localUnsat_implies_entails f7660 [c7641, c7636, c7654, c7659, c7606, c6788, c6323] c7660 unsat7660 (by rfl) a
  have h0 : Entails.eval a c7641 := derived7641 a h
  have h1 : Entails.eval a c7636 := derived7636 a h
  have h2 : Entails.eval a c7654 := derived7654 a h
  have h3 : Entails.eval a c7659 := derived7659 a h
  have h4 : Entails.eval a c7606 := derived7606 a h
  have h5 : Entails.eval a c6788 := h 6787 (by decide)
  have h6 : Entails.eval a c6323 := h 6322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7661 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨20, by decide⟩, true), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, false), (⟨39, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7661 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5198, some c5254, some c5718, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7661 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7661 : lratChecker f7661 p7661 = .success := by decide +kernel
theorem unsat7661 : Unsatisfiable (PosFin 65) f7661 := by
  apply lratCheckerSound f7661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7661
  · intro a ha; simp [p7661] at ha; subst a; trivial
  · exact checked7661
theorem derived7661 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7661 := by
  apply localUnsat_implies_entails f7661 [c5198, c5254, c5718] c7661 unsat7661 (by rfl) a
  have h0 : Entails.eval a c5198 := h 5197 (by decide)
  have h1 : Entails.eval a c5254 := h 5253 (by decide)
  have h2 : Entails.eval a c5718 := h 5717 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7662 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨59, by decide⟩, false), (⟨39, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7662 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6793, some c6929, some c6999, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7662 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7662 : lratChecker f7662 p7662 = .success := by decide +kernel
theorem unsat7662 : Unsatisfiable (PosFin 65) f7662 := by
  apply lratCheckerSound f7662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7662
  · intro a ha; simp [p7662] at ha; subst a; trivial
  · exact checked7662
theorem derived7662 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7662 := by
  apply localUnsat_implies_entails f7662 [c6793, c6929, c6999] c7662 unsat7662 (by rfl) a
  have h0 : Entails.eval a c6793 := h 6792 (by decide)
  have h1 : Entails.eval a c6929 := h 6928 (by decide)
  have h2 : Entails.eval a c6999 := h 6998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7663 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7663 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5438, some c5345, some c5426, some c6043, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7663 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7663 : lratChecker f7663 p7663 = .success := by decide +kernel
theorem unsat7663 : Unsatisfiable (PosFin 65) f7663 := by
  apply lratCheckerSound f7663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7663
  · intro a ha; simp [p7663] at ha; subst a; trivial
  · exact checked7663
theorem derived7663 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7663 := by
  apply localUnsat_implies_entails f7663 [c5438, c5345, c5426, c6043] c7663 unsat7663 (by rfl) a
  have h0 : Entails.eval a c5438 := h 5437 (by decide)
  have h1 : Entails.eval a c5345 := h 5344 (by decide)
  have h2 : Entails.eval a c5426 := h 5425 (by decide)
  have h3 : Entails.eval a c6043 := h 6042 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7664 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨38, by decide⟩, false), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, false), (⟨39, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7664 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5219, some c7661, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7664 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7664 : lratChecker f7664 p7664 = .success := by decide +kernel
theorem unsat7664 : Unsatisfiable (PosFin 65) f7664 := by
  apply lratCheckerSound f7664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7664
  · intro a ha; simp [p7664] at ha; subst a; trivial
  · exact checked7664
theorem derived7664 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7664 := by
  apply localUnsat_implies_entails f7664 [c5219, c7661] c7664 unsat7664 (by rfl) a
  have h0 : Entails.eval a c5219 := h 5218 (by decide)
  have h1 : Entails.eval a c7661 := derived7661 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7665 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨64, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7665 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7641, some c7660, some c7662, some c6854, some c6326, some c7071, some c7260, some c7356, some c7145, some c6756, some c7664, some c7663, some c5161, some c5148, some c5135, some c5537, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7665 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7665 : lratChecker f7665 p7665 = .success := by decide +kernel
theorem unsat7665 : Unsatisfiable (PosFin 65) f7665 := by
  apply lratCheckerSound f7665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7665
  · intro a ha; simp [p7665] at ha; subst a; trivial
  · exact checked7665
theorem derived7665 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7665 := by
  apply localUnsat_implies_entails f7665 [c7641, c7660, c7662, c6854, c6326, c7071, c7260, c7356, c7145, c6756, c7664, c7663, c5161, c5148, c5135, c5537] c7665 unsat7665 (by rfl) a
  have h0 : Entails.eval a c7641 := derived7641 a h
  have h1 : Entails.eval a c7660 := derived7660 a h
  have h2 : Entails.eval a c7662 := derived7662 a h
  have h3 : Entails.eval a c6854 := h 6853 (by decide)
  have h4 : Entails.eval a c6326 := h 6325 (by decide)
  have h5 : Entails.eval a c7071 := h 7070 (by decide)
  have h6 : Entails.eval a c7260 := h 7259 (by decide)
  have h7 : Entails.eval a c7356 := h 7355 (by decide)
  have h8 : Entails.eval a c7145 := h 7144 (by decide)
  have h9 : Entails.eval a c6756 := h 6755 (by decide)
  have h10 : Entails.eval a c7664 := derived7664 a h
  have h11 : Entails.eval a c7663 := derived7663 a h
  have h12 : Entails.eval a c5161 := h 5160 (by decide)
  have h13 : Entails.eval a c5148 := h 5147 (by decide)
  have h14 : Entails.eval a c5135 := h 5134 (by decide)
  have h15 : Entails.eval a c5537 := h 5536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7666 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨59, by decide⟩, false), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7666 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6326, some c6312, some c6313, some c6310, some c7260, some c6807, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7666 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7666 : lratChecker f7666 p7666 = .success := by decide +kernel
theorem unsat7666 : Unsatisfiable (PosFin 65) f7666 := by
  apply lratCheckerSound f7666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7666
  · intro a ha; simp [p7666] at ha; subst a; trivial
  · exact checked7666
theorem derived7666 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7666 := by
  apply localUnsat_implies_entails f7666 [c6326, c6312, c6313, c6310, c7260, c6807] c7666 unsat7666 (by rfl) a
  have h0 : Entails.eval a c6326 := h 6325 (by decide)
  have h1 : Entails.eval a c6312 := h 6311 (by decide)
  have h2 : Entails.eval a c6313 := h 6312 (by decide)
  have h3 : Entails.eval a c6310 := h 6309 (by decide)
  have h4 : Entails.eval a c7260 := h 7259 (by decide)
  have h5 : Entails.eval a c6807 := h 6806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7667 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7667 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7665, some c7666, some c6793, some c6929, some c6342, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7667 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7667 : lratChecker f7667 p7667 = .success := by decide +kernel
theorem unsat7667 : Unsatisfiable (PosFin 65) f7667 := by
  apply lratCheckerSound f7667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7667
  · intro a ha; simp [p7667] at ha; subst a; trivial
  · exact checked7667
theorem derived7667 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7667 := by
  apply localUnsat_implies_entails f7667 [c7665, c7666, c6793, c6929, c6342] c7667 unsat7667 (by rfl) a
  have h0 : Entails.eval a c7665 := derived7665 a h
  have h1 : Entails.eval a c7666 := derived7666 a h
  have h2 : Entails.eval a c6793 := h 6792 (by decide)
  have h3 : Entails.eval a c6929 := h 6928 (by decide)
  have h4 : Entails.eval a c6342 := h 6341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7668 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7668 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6356, some c6352, some c6351, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7668 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7668 : lratChecker f7668 p7668 = .success := by decide +kernel
theorem unsat7668 : Unsatisfiable (PosFin 65) f7668 := by
  apply lratCheckerSound f7668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7668
  · intro a ha; simp [p7668] at ha; subst a; trivial
  · exact checked7668
theorem derived7668 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7668 := by
  apply localUnsat_implies_entails f7668 [c6356, c6352, c6351] c7668 unsat7668 (by rfl) a
  have h0 : Entails.eval a c6356 := h 6355 (by decide)
  have h1 : Entails.eval a c6352 := h 6351 (by decide)
  have h2 : Entails.eval a c6351 := h 6350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7669 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, true), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7669 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6787, some c6788, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7669 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7669 : lratChecker f7669 p7669 = .success := by decide +kernel
theorem unsat7669 : Unsatisfiable (PosFin 65) f7669 := by
  apply lratCheckerSound f7669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7669
  · intro a ha; simp [p7669] at ha; subst a; trivial
  · exact checked7669
theorem derived7669 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7669 := by
  apply localUnsat_implies_entails f7669 [c6787, c6788] c7669 unsat7669 (by rfl) a
  have h0 : Entails.eval a c6787 := h 6786 (by decide)
  have h1 : Entails.eval a c6788 := h 6787 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7670 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7670 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7636, some c7665, some c7667, some c7668, some c7606, some c7669, some c6319, some c6325, some c6316, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7670 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7670 : lratChecker f7670 p7670 = .success := by decide +kernel
theorem unsat7670 : Unsatisfiable (PosFin 65) f7670 := by
  apply lratCheckerSound f7670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7670
  · intro a ha; simp [p7670] at ha; subst a; trivial
  · exact checked7670
theorem derived7670 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7670 := by
  apply localUnsat_implies_entails f7670 [c7636, c7665, c7667, c7668, c7606, c7669, c6319, c6325, c6316] c7670 unsat7670 (by rfl) a
  have h0 : Entails.eval a c7636 := derived7636 a h
  have h1 : Entails.eval a c7665 := derived7665 a h
  have h2 : Entails.eval a c7667 := derived7667 a h
  have h3 : Entails.eval a c7668 := derived7668 a h
  have h4 : Entails.eval a c7606 := derived7606 a h
  have h5 : Entails.eval a c7669 := derived7669 a h
  have h6 : Entails.eval a c6319 := h 6318 (by decide)
  have h7 : Entails.eval a c6325 := h 6324 (by decide)
  have h8 : Entails.eval a c6316 := h 6315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7671 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7671 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6444, some c7080, some c6541, some c7363, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7671 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7671 : lratChecker f7671 p7671 = .success := by decide +kernel
theorem unsat7671 : Unsatisfiable (PosFin 65) f7671 := by
  apply lratCheckerSound f7671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7671
  · intro a ha; simp [p7671] at ha; subst a; trivial
  · exact checked7671
theorem derived7671 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7671 := by
  apply localUnsat_implies_entails f7671 [c6444, c7080, c6541, c7363] c7671 unsat7671 (by rfl) a
  have h0 : Entails.eval a c6444 := h 6443 (by decide)
  have h1 : Entails.eval a c7080 := h 7079 (by decide)
  have h2 : Entails.eval a c6541 := h 6540 (by decide)
  have h3 : Entails.eval a c7363 := h 7362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7672 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨36, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7672 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7670, some c7636, some c7606, some c7669, some c7671, some c7081, some c6945, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7672 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7672 : lratChecker f7672 p7672 = .success := by decide +kernel
theorem unsat7672 : Unsatisfiable (PosFin 65) f7672 := by
  apply lratCheckerSound f7672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7672
  · intro a ha; simp [p7672] at ha; subst a; trivial
  · exact checked7672
theorem derived7672 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7672 := by
  apply localUnsat_implies_entails f7672 [c7670, c7636, c7606, c7669, c7671, c7081, c6945] c7672 unsat7672 (by rfl) a
  have h0 : Entails.eval a c7670 := derived7670 a h
  have h1 : Entails.eval a c7636 := derived7636 a h
  have h2 : Entails.eval a c7606 := derived7606 a h
  have h3 : Entails.eval a c7669 := derived7669 a h
  have h4 : Entails.eval a c7671 := derived7671 a h
  have h5 : Entails.eval a c7081 := h 7080 (by decide)
  have h6 : Entails.eval a c6945 := h 6944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7673 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7673 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7670, some c7672, some c7585, some c6401, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7673 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7673 : lratChecker f7673 p7673 = .success := by decide +kernel
theorem unsat7673 : Unsatisfiable (PosFin 65) f7673 := by
  apply lratCheckerSound f7673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7673
  · intro a ha; simp [p7673] at ha; subst a; trivial
  · exact checked7673
theorem derived7673 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7673 := by
  apply localUnsat_implies_entails f7673 [c7670, c7672, c7585, c6401] c7673 unsat7673 (by rfl) a
  have h0 : Entails.eval a c7670 := derived7670 a h
  have h1 : Entails.eval a c7672 := derived7672 a h
  have h2 : Entails.eval a c7585 := derived7585 a h
  have h3 : Entails.eval a c6401 := h 6400 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7674 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7674 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6401, some c6445, some c7145, some c6528, some c6916, some c6825, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7674 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7674 : lratChecker f7674 p7674 = .success := by decide +kernel
theorem unsat7674 : Unsatisfiable (PosFin 65) f7674 := by
  apply lratCheckerSound f7674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7674
  · intro a ha; simp [p7674] at ha; subst a; trivial
  · exact checked7674
theorem derived7674 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7674 := by
  apply localUnsat_implies_entails f7674 [c6401, c6445, c7145, c6528, c6916, c6825] c7674 unsat7674 (by rfl) a
  have h0 : Entails.eval a c6401 := h 6400 (by decide)
  have h1 : Entails.eval a c6445 := h 6444 (by decide)
  have h2 : Entails.eval a c7145 := h 7144 (by decide)
  have h3 : Entails.eval a c6528 := h 6527 (by decide)
  have h4 : Entails.eval a c6916 := h 6915 (by decide)
  have h5 : Entails.eval a c6825 := h 6824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7675 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨43, by decide⟩, false), (⟨59, by decide⟩, true), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7675 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6808, some c6811, some c7097, some c6541, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7675 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7675 : lratChecker f7675 p7675 = .success := by decide +kernel
theorem unsat7675 : Unsatisfiable (PosFin 65) f7675 := by
  apply lratCheckerSound f7675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7675
  · intro a ha; simp [p7675] at ha; subst a; trivial
  · exact checked7675
theorem derived7675 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7675 := by
  apply localUnsat_implies_entails f7675 [c6808, c6811, c7097, c6541] c7675 unsat7675 (by rfl) a
  have h0 : Entails.eval a c6808 := h 6807 (by decide)
  have h1 : Entails.eval a c6811 := h 6810 (by decide)
  have h2 : Entails.eval a c7097 := h 7096 (by decide)
  have h3 : Entails.eval a c6541 := h 6540 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7676 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7676 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6914, some c6541, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7676 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7676 : lratChecker f7676 p7676 = .success := by decide +kernel
theorem unsat7676 : Unsatisfiable (PosFin 65) f7676 := by
  apply lratCheckerSound f7676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7676
  · intro a ha; simp [p7676] at ha; subst a; trivial
  · exact checked7676
theorem derived7676 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7676 := by
  apply localUnsat_implies_entails f7676 [c6914, c6541] c7676 unsat7676 (by rfl) a
  have h0 : Entails.eval a c6914 := h 6913 (by decide)
  have h1 : Entails.eval a c6541 := h 6540 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7677 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨43, by decide⟩, false), (⟨59, by decide⟩, true), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7677 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7675, some c7676, some c7099, some c7098, some c7244, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7677 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7677 : lratChecker f7677 p7677 = .success := by decide +kernel
theorem unsat7677 : Unsatisfiable (PosFin 65) f7677 := by
  apply lratCheckerSound f7677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7677
  · intro a ha; simp [p7677] at ha; subst a; trivial
  · exact checked7677
theorem derived7677 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7677 := by
  apply localUnsat_implies_entails f7677 [c7675, c7676, c7099, c7098, c7244] c7677 unsat7677 (by rfl) a
  have h0 : Entails.eval a c7675 := derived7675 a h
  have h1 : Entails.eval a c7676 := derived7676 a h
  have h2 : Entails.eval a c7099 := h 7098 (by decide)
  have h3 : Entails.eval a c7098 := h 7097 (by decide)
  have h4 : Entails.eval a c7244 := h 7243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7678 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨59, by decide⟩, true), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7678 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6397, some c6398, some c6396, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7678 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7678 : lratChecker f7678 p7678 = .success := by decide +kernel
theorem unsat7678 : Unsatisfiable (PosFin 65) f7678 := by
  apply lratCheckerSound f7678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7678
  · intro a ha; simp [p7678] at ha; subst a; trivial
  · exact checked7678
theorem derived7678 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7678 := by
  apply localUnsat_implies_entails f7678 [c6397, c6398, c6396] c7678 unsat7678 (by rfl) a
  have h0 : Entails.eval a c6397 := h 6396 (by decide)
  have h1 : Entails.eval a c6398 := h 6397 (by decide)
  have h2 : Entails.eval a c6396 := h 6395 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7679 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨43, by decide⟩, true), (⟨37, by decide⟩, false), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7679 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6538, some c7089, some c7169, some c7467, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7679 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7679 : lratChecker f7679 p7679 = .success := by decide +kernel
theorem unsat7679 : Unsatisfiable (PosFin 65) f7679 := by
  apply lratCheckerSound f7679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7679
  · intro a ha; simp [p7679] at ha; subst a; trivial
  · exact checked7679
theorem derived7679 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7679 := by
  apply localUnsat_implies_entails f7679 [c6538, c7089, c7169, c7467] c7679 unsat7679 (by rfl) a
  have h0 : Entails.eval a c6538 := h 6537 (by decide)
  have h1 : Entails.eval a c7089 := h 7088 (by decide)
  have h2 : Entails.eval a c7169 := h 7168 (by decide)
  have h3 : Entails.eval a c7467 := h 7466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7680 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨54, by decide⟩, true), (⟨60, by decide⟩, true), (⟨41, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7680 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7368, some c7642, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7680 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7680 : lratChecker f7680 p7680 = .success := by decide +kernel
theorem unsat7680 : Unsatisfiable (PosFin 65) f7680 := by
  apply lratCheckerSound f7680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7680
  · intro a ha; simp [p7680] at ha; subst a; trivial
  · exact checked7680
theorem derived7680 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7680 := by
  apply localUnsat_implies_entails f7680 [c7368, c7642] c7680 unsat7680 (by rfl) a
  have h0 : Entails.eval a c7368 := h 7367 (by decide)
  have h1 : Entails.eval a c7642 := derived7642 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7681 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7681 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6539, some c7033, some c7680, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7681 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7681 : lratChecker f7681 p7681 = .success := by decide +kernel
theorem unsat7681 : Unsatisfiable (PosFin 65) f7681 := by
  apply lratCheckerSound f7681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7681
  · intro a ha; simp [p7681] at ha; subst a; trivial
  · exact checked7681
theorem derived7681 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7681 := by
  apply localUnsat_implies_entails f7681 [c6539, c7033, c7680] c7681 unsat7681 (by rfl) a
  have h0 : Entails.eval a c6539 := h 6538 (by decide)
  have h1 : Entails.eval a c7033 := h 7032 (by decide)
  have h2 : Entails.eval a c7680 := derived7680 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7682 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7682 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7636, some c7670, some c7673, some c7674, some c7678, some c7677, some c7681, some c7679, some c6444, some c6541, some c7141, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7682 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7682 : lratChecker f7682 p7682 = .success := by decide +kernel
theorem unsat7682 : Unsatisfiable (PosFin 65) f7682 := by
  apply lratCheckerSound f7682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7682
  · intro a ha; simp [p7682] at ha; subst a; trivial
  · exact checked7682
theorem derived7682 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7682 := by
  apply localUnsat_implies_entails f7682 [c7636, c7670, c7673, c7674, c7678, c7677, c7681, c7679, c6444, c6541, c7141] c7682 unsat7682 (by rfl) a
  have h0 : Entails.eval a c7636 := derived7636 a h
  have h1 : Entails.eval a c7670 := derived7670 a h
  have h2 : Entails.eval a c7673 := derived7673 a h
  have h3 : Entails.eval a c7674 := derived7674 a h
  have h4 : Entails.eval a c7678 := derived7678 a h
  have h5 : Entails.eval a c7677 := derived7677 a h
  have h6 : Entails.eval a c7681 := derived7681 a h
  have h7 : Entails.eval a c7679 := derived7679 a h
  have h8 : Entails.eval a c6444 := h 6443 (by decide)
  have h9 : Entails.eval a c6541 := h 6540 (by decide)
  have h10 : Entails.eval a c7141 := h 7140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7683 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨63, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7683 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7020, some c7103, some c7055, some c7377, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7683 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7683 : lratChecker f7683 p7683 = .success := by decide +kernel
theorem unsat7683 : Unsatisfiable (PosFin 65) f7683 := by
  apply lratCheckerSound f7683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7683
  · intro a ha; simp [p7683] at ha; subst a; trivial
  · exact checked7683
theorem derived7683 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7683 := by
  apply localUnsat_implies_entails f7683 [c7020, c7103, c7055, c7377] c7683 unsat7683 (by rfl) a
  have h0 : Entails.eval a c7020 := h 7019 (by decide)
  have h1 : Entails.eval a c7103 := h 7102 (by decide)
  have h2 : Entails.eval a c7055 := h 7054 (by decide)
  have h3 : Entails.eval a c7377 := h 7376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7684 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨35, by decide⟩, false), (⟨44, by decide⟩, false), (⟨36, by decide⟩, true), (⟨41, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7684 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7081, some c6945, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7684 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7684 : lratChecker f7684 p7684 = .success := by decide +kernel
theorem unsat7684 : Unsatisfiable (PosFin 65) f7684 := by
  apply lratCheckerSound f7684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7684
  · intro a ha; simp [p7684] at ha; subst a; trivial
  · exact checked7684
theorem derived7684 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7684 := by
  apply localUnsat_implies_entails f7684 [c7081, c6945] c7684 unsat7684 (by rfl) a
  have h0 : Entails.eval a c7081 := h 7080 (by decide)
  have h1 : Entails.eval a c6945 := h 6944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7685 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨59, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7685 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7682, some c7636, some c7683, some c7606, some c7669, some c6938, some c7684, some c6618, some c6988, some c7080, some c6663, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7685 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7685 : lratChecker f7685 p7685 = .success := by decide +kernel
theorem unsat7685 : Unsatisfiable (PosFin 65) f7685 := by
  apply lratCheckerSound f7685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7685
  · intro a ha; simp [p7685] at ha; subst a; trivial
  · exact checked7685
theorem derived7685 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7685 := by
  apply localUnsat_implies_entails f7685 [c7682, c7636, c7683, c7606, c7669, c6938, c7684, c6618, c6988, c7080, c6663] c7685 unsat7685 (by rfl) a
  have h0 : Entails.eval a c7682 := derived7682 a h
  have h1 : Entails.eval a c7636 := derived7636 a h
  have h2 : Entails.eval a c7683 := derived7683 a h
  have h3 : Entails.eval a c7606 := derived7606 a h
  have h4 : Entails.eval a c7669 := derived7669 a h
  have h5 : Entails.eval a c6938 := h 6937 (by decide)
  have h6 : Entails.eval a c7684 := derived7684 a h
  have h7 : Entails.eval a c6618 := h 6617 (by decide)
  have h8 : Entails.eval a c6988 := h 6987 (by decide)
  have h9 : Entails.eval a c7080 := h 7079 (by decide)
  have h10 : Entails.eval a c6663 := h 6662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7686 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨54, by decide⟩, true), (⟨48, by decide⟩, false), (⟨60, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7686 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7054, some c6699, some c7513, some c6617, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7686 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7686 : lratChecker f7686 p7686 = .success := by decide +kernel
theorem unsat7686 : Unsatisfiable (PosFin 65) f7686 := by
  apply lratCheckerSound f7686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7686
  · intro a ha; simp [p7686] at ha; subst a; trivial
  · exact checked7686
theorem derived7686 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7686 := by
  apply localUnsat_implies_entails f7686 [c7054, c6699, c7513, c6617] c7686 unsat7686 (by rfl) a
  have h0 : Entails.eval a c7054 := h 7053 (by decide)
  have h1 : Entails.eval a c6699 := h 6698 (by decide)
  have h2 : Entails.eval a c7513 := h 7512 (by decide)
  have h3 : Entails.eval a c6617 := h 6616 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7687 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7687 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7682, some c7636, some c7685, some c7680, some c7686, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7687 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7687 : lratChecker f7687 p7687 = .success := by decide +kernel
theorem unsat7687 : Unsatisfiable (PosFin 65) f7687 := by
  apply lratCheckerSound f7687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7687
  · intro a ha; simp [p7687] at ha; subst a; trivial
  · exact checked7687
theorem derived7687 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7687 := by
  apply localUnsat_implies_entails f7687 [c7682, c7636, c7685, c7680, c7686] c7687 unsat7687 (by rfl) a
  have h0 : Entails.eval a c7682 := derived7682 a h
  have h1 : Entails.eval a c7636 := derived7636 a h
  have h2 : Entails.eval a c7685 := derived7685 a h
  have h3 : Entails.eval a c7680 := derived7680 a h
  have h4 : Entails.eval a c7686 := derived7686 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7688 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨63, by decide⟩, false), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7688 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7514, some c7059, some c6702, some c6624, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7688 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7688 : lratChecker f7688 p7688 = .success := by decide +kernel
theorem unsat7688 : Unsatisfiable (PosFin 65) f7688 := by
  apply lratCheckerSound f7688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7688
  · intro a ha; simp [p7688] at ha; subst a; trivial
  · exact checked7688
theorem derived7688 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7688 := by
  apply localUnsat_implies_entails f7688 [c7514, c7059, c6702, c6624] c7688 unsat7688 (by rfl) a
  have h0 : Entails.eval a c7514 := h 7513 (by decide)
  have h1 : Entails.eval a c7059 := h 7058 (by decide)
  have h2 : Entails.eval a c6702 := h 6701 (by decide)
  have h3 : Entails.eval a c6624 := h 6623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7689 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7689 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7362, some c6744, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7689 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7689 : lratChecker f7689 p7689 = .success := by decide +kernel
theorem unsat7689 : Unsatisfiable (PosFin 65) f7689 := by
  apply lratCheckerSound f7689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7689
  · intro a ha; simp [p7689] at ha; subst a; trivial
  · exact checked7689
theorem derived7689 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7689 := by
  apply localUnsat_implies_entails f7689 [c7362, c6744] c7689 unsat7689 (by rfl) a
  have h0 : Entails.eval a c7362 := h 7361 (by decide)
  have h1 : Entails.eval a c6744 := h 6743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7690 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7690 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7687, some c7682, some c7688, some c7636, some c6418, some c6457, some c7430, some c7023, some c6624, some c6528, some c7585, some c7591, some c7622, some c7689, some c6380, some c6976, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7690 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7690 : lratChecker f7690 p7690 = .success := by decide +kernel
theorem unsat7690 : Unsatisfiable (PosFin 65) f7690 := by
  apply lratCheckerSound f7690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7690
  · intro a ha; simp [p7690] at ha; subst a; trivial
  · exact checked7690
theorem derived7690 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7690 := by
  apply localUnsat_implies_entails f7690 [c7687, c7682, c7688, c7636, c6418, c6457, c7430, c7023, c6624, c6528, c7585, c7591, c7622, c7689, c6380, c6976] c7690 unsat7690 (by rfl) a
  have h0 : Entails.eval a c7687 := derived7687 a h
  have h1 : Entails.eval a c7682 := derived7682 a h
  have h2 : Entails.eval a c7688 := derived7688 a h
  have h3 : Entails.eval a c7636 := derived7636 a h
  have h4 : Entails.eval a c6418 := h 6417 (by decide)
  have h5 : Entails.eval a c6457 := h 6456 (by decide)
  have h6 : Entails.eval a c7430 := h 7429 (by decide)
  have h7 : Entails.eval a c7023 := h 7022 (by decide)
  have h8 : Entails.eval a c6624 := h 6623 (by decide)
  have h9 : Entails.eval a c6528 := h 6527 (by decide)
  have h10 : Entails.eval a c7585 := derived7585 a h
  have h11 : Entails.eval a c7591 := derived7591 a h
  have h12 : Entails.eval a c7622 := derived7622 a h
  have h13 : Entails.eval a c7689 := derived7689 a h
  have h14 : Entails.eval a c6380 := h 6379 (by decide)
  have h15 : Entails.eval a c6976 := h 6975 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7691 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7691 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7682, some c7687, some c7688, some c6887, some c7690, some c7370, some c6326, some c7023, some c7071, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7691 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7691 : lratChecker f7691 p7691 = .success := by decide +kernel
theorem unsat7691 : Unsatisfiable (PosFin 65) f7691 := by
  apply lratCheckerSound f7691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7691
  · intro a ha; simp [p7691] at ha; subst a; trivial
  · exact checked7691
theorem derived7691 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7691 := by
  apply localUnsat_implies_entails f7691 [c7682, c7687, c7688, c6887, c7690, c7370, c6326, c7023, c7071] c7691 unsat7691 (by rfl) a
  have h0 : Entails.eval a c7682 := derived7682 a h
  have h1 : Entails.eval a c7687 := derived7687 a h
  have h2 : Entails.eval a c7688 := derived7688 a h
  have h3 : Entails.eval a c6887 := h 6886 (by decide)
  have h4 : Entails.eval a c7690 := derived7690 a h
  have h5 : Entails.eval a c7370 := h 7369 (by decide)
  have h6 : Entails.eval a c6326 := h 6325 (by decide)
  have h7 : Entails.eval a c7023 := h 7022 (by decide)
  have h8 : Entails.eval a c7071 := h 7070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7692 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨41, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7692 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7591, some c7581, some c6418, some c7585, some c6651, some c6612, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7692 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7692 : lratChecker f7692 p7692 = .success := by decide +kernel
theorem unsat7692 : Unsatisfiable (PosFin 65) f7692 := by
  apply lratCheckerSound f7692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7692
  · intro a ha; simp [p7692] at ha; subst a; trivial
  · exact checked7692
theorem derived7692 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7692 := by
  apply localUnsat_implies_entails f7692 [c7591, c7581, c6418, c7585, c6651, c6612] c7692 unsat7692 (by rfl) a
  have h0 : Entails.eval a c7591 := derived7591 a h
  have h1 : Entails.eval a c7581 := derived7581 a h
  have h2 : Entails.eval a c6418 := h 6417 (by decide)
  have h3 : Entails.eval a c7585 := derived7585 a h
  have h4 : Entails.eval a c6651 := h 6650 (by decide)
  have h5 : Entails.eval a c6612 := h 6611 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7693 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨41, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7693 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6418, some c6457, some c7129, some c7298, some c7023, some c7240, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7693 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7693 : lratChecker f7693 p7693 = .success := by decide +kernel
theorem unsat7693 : Unsatisfiable (PosFin 65) f7693 := by
  apply lratCheckerSound f7693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7693
  · intro a ha; simp [p7693] at ha; subst a; trivial
  · exact checked7693
theorem derived7693 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7693 := by
  apply localUnsat_implies_entails f7693 [c6418, c6457, c7129, c7298, c7023, c7240] c7693 unsat7693 (by rfl) a
  have h0 : Entails.eval a c6418 := h 6417 (by decide)
  have h1 : Entails.eval a c6457 := h 6456 (by decide)
  have h2 : Entails.eval a c7129 := h 7128 (by decide)
  have h3 : Entails.eval a c7298 := h 7297 (by decide)
  have h4 : Entails.eval a c7023 := h 7022 (by decide)
  have h5 : Entails.eval a c7240 := h 7239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7694 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7694 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7691, some c7636, some c7692, some c7693, some c6495, some c6285, some c7668, some c6728, some c6724, some c6722, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7694 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7694 : lratChecker f7694 p7694 = .success := by decide +kernel
theorem unsat7694 : Unsatisfiable (PosFin 65) f7694 := by
  apply lratCheckerSound f7694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7694
  · intro a ha; simp [p7694] at ha; subst a; trivial
  · exact checked7694
theorem derived7694 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7694 := by
  apply localUnsat_implies_entails f7694 [c7691, c7636, c7692, c7693, c6495, c6285, c7668, c6728, c6724, c6722] c7694 unsat7694 (by rfl) a
  have h0 : Entails.eval a c7691 := derived7691 a h
  have h1 : Entails.eval a c7636 := derived7636 a h
  have h2 : Entails.eval a c7692 := derived7692 a h
  have h3 : Entails.eval a c7693 := derived7693 a h
  have h4 : Entails.eval a c6495 := h 6494 (by decide)
  have h5 : Entails.eval a c6285 := h 6284 (by decide)
  have h6 : Entails.eval a c7668 := derived7668 a h
  have h7 : Entails.eval a c6728 := h 6727 (by decide)
  have h8 : Entails.eval a c6724 := h 6723 (by decide)
  have h9 : Entails.eval a c6722 := h 6721 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7695 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7695 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7691, some c7636, some c6495, some c6285, some c7668, some c6728, some c6724, some c6722, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7695 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7695 : lratChecker f7695 p7695 = .success := by decide +kernel
theorem unsat7695 : Unsatisfiable (PosFin 65) f7695 := by
  apply lratCheckerSound f7695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7695
  · intro a ha; simp [p7695] at ha; subst a; trivial
  · exact checked7695
theorem derived7695 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7695 := by
  apply localUnsat_implies_entails f7695 [c7691, c7636, c6495, c6285, c7668, c6728, c6724, c6722] c7695 unsat7695 (by rfl) a
  have h0 : Entails.eval a c7691 := derived7691 a h
  have h1 : Entails.eval a c7636 := derived7636 a h
  have h2 : Entails.eval a c6495 := h 6494 (by decide)
  have h3 : Entails.eval a c6285 := h 6284 (by decide)
  have h4 : Entails.eval a c7668 := derived7668 a h
  have h5 : Entails.eval a c6728 := h 6727 (by decide)
  have h6 : Entails.eval a c6724 := h 6723 (by decide)
  have h7 : Entails.eval a c6722 := h 6721 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7696 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7696 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7694, some c7688, some c7691, some c7038, some c7695, some c6401, some c6528, some c7210, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7696 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7696 : lratChecker f7696 p7696 = .success := by decide +kernel
theorem unsat7696 : Unsatisfiable (PosFin 65) f7696 := by
  apply lratCheckerSound f7696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7696
  · intro a ha; simp [p7696] at ha; subst a; trivial
  · exact checked7696
theorem derived7696 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7696 := by
  apply localUnsat_implies_entails f7696 [c7694, c7688, c7691, c7038, c7695, c6401, c6528, c7210] c7696 unsat7696 (by rfl) a
  have h0 : Entails.eval a c7694 := derived7694 a h
  have h1 : Entails.eval a c7688 := derived7688 a h
  have h2 : Entails.eval a c7691 := derived7691 a h
  have h3 : Entails.eval a c7038 := h 7037 (by decide)
  have h4 : Entails.eval a c7695 := derived7695 a h
  have h5 : Entails.eval a c6401 := h 6400 (by decide)
  have h6 : Entails.eval a c6528 := h 6527 (by decide)
  have h7 : Entails.eval a c7210 := h 7209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7697 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7697 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7694, some c7688, some c7696, some c7591, some c7581, some c7585, some c6401, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7697 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7697 : lratChecker f7697 p7697 = .success := by decide +kernel
theorem unsat7697 : Unsatisfiable (PosFin 65) f7697 := by
  apply lratCheckerSound f7697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7697
  · intro a ha; simp [p7697] at ha; subst a; trivial
  · exact checked7697
theorem derived7697 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7697 := by
  apply localUnsat_implies_entails f7697 [c7694, c7688, c7696, c7591, c7581, c7585, c6401] c7697 unsat7697 (by rfl) a
  have h0 : Entails.eval a c7694 := derived7694 a h
  have h1 : Entails.eval a c7688 := derived7688 a h
  have h2 : Entails.eval a c7696 := derived7696 a h
  have h3 : Entails.eval a c7591 := derived7591 a h
  have h4 : Entails.eval a c7581 := derived7581 a h
  have h5 : Entails.eval a c7585 := derived7585 a h
  have h6 : Entails.eval a c6401 := h 6400 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7698 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨36, by decide⟩, true), (⟨41, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7698 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7206, some c6618, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7698 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7698 : lratChecker f7698 p7698 = .success := by decide +kernel
theorem unsat7698 : Unsatisfiable (PosFin 65) f7698 := by
  apply lratCheckerSound f7698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7698
  · intro a ha; simp [p7698] at ha; subst a; trivial
  · exact checked7698
theorem derived7698 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7698 := by
  apply localUnsat_implies_entails f7698 [c7206, c6618] c7698 unsat7698 (by rfl) a
  have h0 : Entails.eval a c7206 := h 7205 (by decide)
  have h1 : Entails.eval a c6618 := h 6617 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7699 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7699 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6444, some c7115, some c6663, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7699 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7699 : lratChecker f7699 p7699 = .success := by decide +kernel
theorem unsat7699 : Unsatisfiable (PosFin 65) f7699 := by
  apply lratCheckerSound f7699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7699
  · intro a ha; simp [p7699] at ha; subst a; trivial
  · exact checked7699
theorem derived7699 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7699 := by
  apply localUnsat_implies_entails f7699 [c6444, c7115, c6663] c7699 unsat7699 (by rfl) a
  have h0 : Entails.eval a c6444 := h 6443 (by decide)
  have h1 : Entails.eval a c7115 := h 7114 (by decide)
  have h2 : Entails.eval a c6663 := h 6662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7700 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7700 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7697, some c7691, some c7636, some c6710, some c7206, some c7699, some c6649, some c6429, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7700 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7700 : lratChecker f7700 p7700 = .success := by decide +kernel
theorem unsat7700 : Unsatisfiable (PosFin 65) f7700 := by
  apply lratCheckerSound f7700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7700
  · intro a ha; simp [p7700] at ha; subst a; trivial
  · exact checked7700
theorem derived7700 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7700 := by
  apply localUnsat_implies_entails f7700 [c7697, c7691, c7636, c6710, c7206, c7699, c6649, c6429] c7700 unsat7700 (by rfl) a
  have h0 : Entails.eval a c7697 := derived7697 a h
  have h1 : Entails.eval a c7691 := derived7691 a h
  have h2 : Entails.eval a c7636 := derived7636 a h
  have h3 : Entails.eval a c6710 := h 6709 (by decide)
  have h4 : Entails.eval a c7206 := h 7205 (by decide)
  have h5 : Entails.eval a c7699 := derived7699 a h
  have h6 : Entails.eval a c6649 := h 6648 (by decide)
  have h7 : Entails.eval a c6429 := h 6428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7701 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7701 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7697, some c7691, some c7636, some c7700, some c6709, some c7205, some c7699, some c6649, some c6429, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7701 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7701 : lratChecker f7701 p7701 = .success := by decide +kernel
theorem unsat7701 : Unsatisfiable (PosFin 65) f7701 := by
  apply lratCheckerSound f7701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7701
  · intro a ha; simp [p7701] at ha; subst a; trivial
  · exact checked7701
theorem derived7701 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7701 := by
  apply localUnsat_implies_entails f7701 [c7697, c7691, c7636, c7700, c6709, c7205, c7699, c6649, c6429] c7701 unsat7701 (by rfl) a
  have h0 : Entails.eval a c7697 := derived7697 a h
  have h1 : Entails.eval a c7691 := derived7691 a h
  have h2 : Entails.eval a c7636 := derived7636 a h
  have h3 : Entails.eval a c7700 := derived7700 a h
  have h4 : Entails.eval a c6709 := h 6708 (by decide)
  have h5 : Entails.eval a c7205 := h 7204 (by decide)
  have h6 : Entails.eval a c7699 := derived7699 a h
  have h7 : Entails.eval a c6649 := h 6648 (by decide)
  have h8 : Entails.eval a c6429 := h 6428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7702 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7702 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7697, some c7691, some c7636, some c7701, some c7698, some c7205, some c6617, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7702 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7702 : lratChecker f7702 p7702 = .success := by decide +kernel
theorem unsat7702 : Unsatisfiable (PosFin 65) f7702 := by
  apply lratCheckerSound f7702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7702
  · intro a ha; simp [p7702] at ha; subst a; trivial
  · exact checked7702
theorem derived7702 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7702 := by
  apply localUnsat_implies_entails f7702 [c7697, c7691, c7636, c7701, c7698, c7205, c6617] c7702 unsat7702 (by rfl) a
  have h0 : Entails.eval a c7697 := derived7697 a h
  have h1 : Entails.eval a c7691 := derived7691 a h
  have h2 : Entails.eval a c7636 := derived7636 a h
  have h3 : Entails.eval a c7701 := derived7701 a h
  have h4 : Entails.eval a c7698 := derived7698 a h
  have h5 : Entails.eval a c7205 := h 7204 (by decide)
  have h6 : Entails.eval a c6617 := h 6616 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7703 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨37, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7703 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6609, some c6611, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7703 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7703 : lratChecker f7703 p7703 = .success := by decide +kernel
theorem unsat7703 : Unsatisfiable (PosFin 65) f7703 := by
  apply lratCheckerSound f7703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7703
  · intro a ha; simp [p7703] at ha; subst a; trivial
  · exact checked7703
theorem derived7703 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7703 := by
  apply localUnsat_implies_entails f7703 [c6609, c6611] c7703 unsat7703 (by rfl) a
  have h0 : Entails.eval a c6609 := h 6608 (by decide)
  have h1 : Entails.eval a c6611 := h 6610 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7704 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7704 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7697, some c7691, some c7636, some c7702, some c7678, some c7703, some c6709, some c6710, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7704 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7704 : lratChecker f7704 p7704 = .success := by decide +kernel
theorem unsat7704 : Unsatisfiable (PosFin 65) f7704 := by
  apply lratCheckerSound f7704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7704
  · intro a ha; simp [p7704] at ha; subst a; trivial
  · exact checked7704
theorem derived7704 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7704 := by
  apply localUnsat_implies_entails f7704 [c7697, c7691, c7636, c7702, c7678, c7703, c6709, c6710] c7704 unsat7704 (by rfl) a
  have h0 : Entails.eval a c7697 := derived7697 a h
  have h1 : Entails.eval a c7691 := derived7691 a h
  have h2 : Entails.eval a c7636 := derived7636 a h
  have h3 : Entails.eval a c7702 := derived7702 a h
  have h4 : Entails.eval a c7678 := derived7678 a h
  have h5 : Entails.eval a c7703 := derived7703 a h
  have h6 : Entails.eval a c6709 := h 6708 (by decide)
  have h7 : Entails.eval a c6710 := h 6709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7705 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨41, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7705 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6281, some c6282, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7705 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7705 : lratChecker f7705 p7705 = .success := by decide +kernel
theorem unsat7705 : Unsatisfiable (PosFin 65) f7705 := by
  apply lratCheckerSound f7705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7705
  · intro a ha; simp [p7705] at ha; subst a; trivial
  · exact checked7705
theorem derived7705 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7705 := by
  apply localUnsat_implies_entails f7705 [c6281, c6282] c7705 unsat7705 (by rfl) a
  have h0 : Entails.eval a c6281 := h 6280 (by decide)
  have h1 : Entails.eval a c6282 := h 6281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7706 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7706 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7697, some c7691, some c7636, some c7704, some c7705, some c7703, some c7698, some c7205, some c6617, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7706 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7706 : lratChecker f7706 p7706 = .success := by decide +kernel
theorem unsat7706 : Unsatisfiable (PosFin 65) f7706 := by
  apply lratCheckerSound f7706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7706
  · intro a ha; simp [p7706] at ha; subst a; trivial
  · exact checked7706
theorem derived7706 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7706 := by
  apply localUnsat_implies_entails f7706 [c7697, c7691, c7636, c7704, c7705, c7703, c7698, c7205, c6617] c7706 unsat7706 (by rfl) a
  have h0 : Entails.eval a c7697 := derived7697 a h
  have h1 : Entails.eval a c7691 := derived7691 a h
  have h2 : Entails.eval a c7636 := derived7636 a h
  have h3 : Entails.eval a c7704 := derived7704 a h
  have h4 : Entails.eval a c7705 := derived7705 a h
  have h5 : Entails.eval a c7703 := derived7703 a h
  have h6 : Entails.eval a c7698 := derived7698 a h
  have h7 : Entails.eval a c7205 := h 7204 (by decide)
  have h8 : Entails.eval a c6617 := h 6616 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7707 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7707 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7636, some c7691, some c7697, some c7705, some c7706, some c7668, some c7205, some c6335, some c6737, some c6728, some c6727, some c6736, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7707 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7707 : lratChecker f7707 p7707 = .success := by decide +kernel
theorem unsat7707 : Unsatisfiable (PosFin 65) f7707 := by
  apply lratCheckerSound f7707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7707
  · intro a ha; simp [p7707] at ha; subst a; trivial
  · exact checked7707
theorem derived7707 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7707 := by
  apply localUnsat_implies_entails f7707 [c7636, c7691, c7697, c7705, c7706, c7668, c7205, c6335, c6737, c6728, c6727, c6736] c7707 unsat7707 (by rfl) a
  have h0 : Entails.eval a c7636 := derived7636 a h
  have h1 : Entails.eval a c7691 := derived7691 a h
  have h2 : Entails.eval a c7697 := derived7697 a h
  have h3 : Entails.eval a c7705 := derived7705 a h
  have h4 : Entails.eval a c7706 := derived7706 a h
  have h5 : Entails.eval a c7668 := derived7668 a h
  have h6 : Entails.eval a c7205 := h 7204 (by decide)
  have h7 : Entails.eval a c6335 := h 6334 (by decide)
  have h8 : Entails.eval a c6737 := h 6736 (by decide)
  have h9 : Entails.eval a c6728 := h 6727 (by decide)
  have h10 : Entails.eval a c6727 := h 6726 (by decide)
  have h11 : Entails.eval a c6736 := h 6735 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7708 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7708 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6493, some c6721, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7708 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7708 : lratChecker f7708 p7708 = .success := by decide +kernel
theorem unsat7708 : Unsatisfiable (PosFin 65) f7708 := by
  apply lratCheckerSound f7708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7708
  · intro a ha; simp [p7708] at ha; subst a; trivial
  · exact checked7708
theorem derived7708 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7708 := by
  apply localUnsat_implies_entails f7708 [c6493, c6721] c7708 unsat7708 (by rfl) a
  have h0 : Entails.eval a c6493 := h 6492 (by decide)
  have h1 : Entails.eval a c6721 := h 6720 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7709 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7709 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7706, some c7697, some c7691, some c7636, some c7668, some c7705, some c7708, some c6335, some c7707, some c6633, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7709 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7709 : lratChecker f7709 p7709 = .success := by decide +kernel
theorem unsat7709 : Unsatisfiable (PosFin 65) f7709 := by
  apply lratCheckerSound f7709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7709
  · intro a ha; simp [p7709] at ha; subst a; trivial
  · exact checked7709
theorem derived7709 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7709 := by
  apply localUnsat_implies_entails f7709 [c7706, c7697, c7691, c7636, c7668, c7705, c7708, c6335, c7707, c6633] c7709 unsat7709 (by rfl) a
  have h0 : Entails.eval a c7706 := derived7706 a h
  have h1 : Entails.eval a c7697 := derived7697 a h
  have h2 : Entails.eval a c7691 := derived7691 a h
  have h3 : Entails.eval a c7636 := derived7636 a h
  have h4 : Entails.eval a c7668 := derived7668 a h
  have h5 : Entails.eval a c7705 := derived7705 a h
  have h6 : Entails.eval a c7708 := derived7708 a h
  have h7 : Entails.eval a c6335 := h 6334 (by decide)
  have h8 : Entails.eval a c7707 := derived7707 a h
  have h9 : Entails.eval a c6633 := h 6632 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7710 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7710 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7678, some c7683, some c7018, some c6365, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7710 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7710 : lratChecker f7710 p7710 = .success := by decide +kernel
theorem unsat7710 : Unsatisfiable (PosFin 65) f7710 := by
  apply lratCheckerSound f7710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7710
  · intro a ha; simp [p7710] at ha; subst a; trivial
  · exact checked7710
theorem derived7710 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7710 := by
  apply localUnsat_implies_entails f7710 [c7678, c7683, c7018, c6365] c7710 unsat7710 (by rfl) a
  have h0 : Entails.eval a c7678 := derived7678 a h
  have h1 : Entails.eval a c7683 := derived7683 a h
  have h2 : Entails.eval a c7018 := h 7017 (by decide)
  have h3 : Entails.eval a c6365 := h 6364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7711 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨41, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7711 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7205, some c6523, some c6551, some c7033, some c7090, some c6454, some c6899, some c6864, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7711 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7711 : lratChecker f7711 p7711 = .success := by decide +kernel
theorem unsat7711 : Unsatisfiable (PosFin 65) f7711 := by
  apply lratCheckerSound f7711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7711
  · intro a ha; simp [p7711] at ha; subst a; trivial
  · exact checked7711
theorem derived7711 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7711 := by
  apply localUnsat_implies_entails f7711 [c7205, c6523, c6551, c7033, c7090, c6454, c6899, c6864] c7711 unsat7711 (by rfl) a
  have h0 : Entails.eval a c7205 := h 7204 (by decide)
  have h1 : Entails.eval a c6523 := h 6522 (by decide)
  have h2 : Entails.eval a c6551 := h 6550 (by decide)
  have h3 : Entails.eval a c7033 := h 7032 (by decide)
  have h4 : Entails.eval a c7090 := h 7089 (by decide)
  have h5 : Entails.eval a c6454 := h 6453 (by decide)
  have h6 : Entails.eval a c6899 := h 6898 (by decide)
  have h7 : Entails.eval a c6864 := h 6863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7712 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7712 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7636, some c7691, some c7697, some c7706, some c7709, some c7710, some c7711, some c7193, some c7206, some c7683, some c7679, some c6735, some c6444, some c6554, some c6663, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7712 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7712 : lratChecker f7712 p7712 = .success := by decide +kernel
theorem unsat7712 : Unsatisfiable (PosFin 65) f7712 := by
  apply lratCheckerSound f7712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7712
  · intro a ha; simp [p7712] at ha; subst a; trivial
  · exact checked7712
theorem derived7712 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7712 := by
  apply localUnsat_implies_entails f7712 [c7636, c7691, c7697, c7706, c7709, c7710, c7711, c7193, c7206, c7683, c7679, c6735, c6444, c6554, c6663] c7712 unsat7712 (by rfl) a
  have h0 : Entails.eval a c7636 := derived7636 a h
  have h1 : Entails.eval a c7691 := derived7691 a h
  have h2 : Entails.eval a c7697 := derived7697 a h
  have h3 : Entails.eval a c7706 := derived7706 a h
  have h4 : Entails.eval a c7709 := derived7709 a h
  have h5 : Entails.eval a c7710 := derived7710 a h
  have h6 : Entails.eval a c7711 := derived7711 a h
  have h7 : Entails.eval a c7193 := h 7192 (by decide)
  have h8 : Entails.eval a c7206 := h 7205 (by decide)
  have h9 : Entails.eval a c7683 := derived7683 a h
  have h10 : Entails.eval a c7679 := derived7679 a h
  have h11 : Entails.eval a c6735 := h 6734 (by decide)
  have h12 : Entails.eval a c6444 := h 6443 (by decide)
  have h13 : Entails.eval a c6554 := h 6553 (by decide)
  have h14 : Entails.eval a c6663 := h 6662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7713 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7713 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7127, some c6429, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7713 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7713 : lratChecker f7713 p7713 = .success := by decide +kernel
theorem unsat7713 : Unsatisfiable (PosFin 65) f7713 := by
  apply lratCheckerSound f7713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7713
  · intro a ha; simp [p7713] at ha; subst a; trivial
  · exact checked7713
theorem derived7713 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7713 := by
  apply localUnsat_implies_entails f7713 [c7127, c6429] c7713 unsat7713 (by rfl) a
  have h0 : Entails.eval a c7127 := h 7126 (by decide)
  have h1 : Entails.eval a c6429 := h 6428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7714 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨60, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7714 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7713, some c6428, some c7141, some c6524, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7714 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7714 : lratChecker f7714 p7714 = .success := by decide +kernel
theorem unsat7714 : Unsatisfiable (PosFin 65) f7714 := by
  apply lratCheckerSound f7714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7714
  · intro a ha; simp [p7714] at ha; subst a; trivial
  · exact checked7714
theorem derived7714 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7714 := by
  apply localUnsat_implies_entails f7714 [c7713, c6428, c7141, c6524] c7714 unsat7714 (by rfl) a
  have h0 : Entails.eval a c7713 := derived7713 a h
  have h1 : Entails.eval a c6428 := h 6427 (by decide)
  have h2 : Entails.eval a c7141 := h 7140 (by decide)
  have h3 : Entails.eval a c6524 := h 6523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7715 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨60, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7715 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7714, some c7204, some c7208, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7715 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7715 : lratChecker f7715 p7715 = .success := by decide +kernel
theorem unsat7715 : Unsatisfiable (PosFin 65) f7715 := by
  apply lratCheckerSound f7715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7715
  · intro a ha; simp [p7715] at ha; subst a; trivial
  · exact checked7715
theorem derived7715 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7715 := by
  apply localUnsat_implies_entails f7715 [c7714, c7204, c7208] c7715 unsat7715 (by rfl) a
  have h0 : Entails.eval a c7714 := derived7714 a h
  have h1 : Entails.eval a c7204 := h 7203 (by decide)
  have h2 : Entails.eval a c7208 := h 7207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7716 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨46, by decide⟩, false), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7716 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6821, some c7184, some c6885, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7716 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7716 : lratChecker f7716 p7716 = .success := by decide +kernel
theorem unsat7716 : Unsatisfiable (PosFin 65) f7716 := by
  apply lratCheckerSound f7716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7716
  · intro a ha; simp [p7716] at ha; subst a; trivial
  · exact checked7716
theorem derived7716 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7716 := by
  apply localUnsat_implies_entails f7716 [c6821, c7184, c6885] c7716 unsat7716 (by rfl) a
  have h0 : Entails.eval a c6821 := h 6820 (by decide)
  have h1 : Entails.eval a c7184 := h 7183 (by decide)
  have h2 : Entails.eval a c6885 := h 6884 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7717 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7717 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7716, some c6822, some c7185, some c6886, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7717 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7717 : lratChecker f7717 p7717 = .success := by decide +kernel
theorem unsat7717 : Unsatisfiable (PosFin 65) f7717 := by
  apply lratCheckerSound f7717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7717
  · intro a ha; simp [p7717] at ha; subst a; trivial
  · exact checked7717
theorem derived7717 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7717 := by
  apply localUnsat_implies_entails f7717 [c7716, c6822, c7185, c6886] c7717 unsat7717 (by rfl) a
  have h0 : Entails.eval a c7716 := derived7716 a h
  have h1 : Entails.eval a c6822 := h 6821 (by decide)
  have h2 : Entails.eval a c7185 := h 7184 (by decide)
  have h3 : Entails.eval a c6886 := h 6885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7718 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨46, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7718 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6429, some c6525, some c7142, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7718 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7718 : lratChecker f7718 p7718 = .success := by decide +kernel
theorem unsat7718 : Unsatisfiable (PosFin 65) f7718 := by
  apply lratCheckerSound f7718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7718
  · intro a ha; simp [p7718] at ha; subst a; trivial
  · exact checked7718
theorem derived7718 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7718 := by
  apply localUnsat_implies_entails f7718 [c6429, c6525, c7142] c7718 unsat7718 (by rfl) a
  have h0 : Entails.eval a c6429 := h 6428 (by decide)
  have h1 : Entails.eval a c6525 := h 6524 (by decide)
  have h2 : Entails.eval a c7142 := h 7141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7719 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨60, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7719 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7718, some c6524, some c6428, some c7141, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7719 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7719 : lratChecker f7719 p7719 = .success := by decide +kernel
theorem unsat7719 : Unsatisfiable (PosFin 65) f7719 := by
  apply lratCheckerSound f7719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7719
  · intro a ha; simp [p7719] at ha; subst a; trivial
  · exact checked7719
theorem derived7719 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7719 := by
  apply localUnsat_implies_entails f7719 [c7718, c6524, c6428, c7141] c7719 unsat7719 (by rfl) a
  have h0 : Entails.eval a c7718 := derived7718 a h
  have h1 : Entails.eval a c6524 := h 6523 (by decide)
  have h2 : Entails.eval a c6428 := h 6427 (by decide)
  have h3 : Entails.eval a c7141 := h 7140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7720 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7720 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7719, some c7717, some c7711, some c7715, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7720 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7720 : lratChecker f7720 p7720 = .success := by decide +kernel
theorem unsat7720 : Unsatisfiable (PosFin 65) f7720 := by
  apply lratCheckerSound f7720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7720
  · intro a ha; simp [p7720] at ha; subst a; trivial
  · exact checked7720
theorem derived7720 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7720 := by
  apply localUnsat_implies_entails f7720 [c7719, c7717, c7711, c7715] c7720 unsat7720 (by rfl) a
  have h0 : Entails.eval a c7719 := derived7719 a h
  have h1 : Entails.eval a c7717 := derived7717 a h
  have h2 : Entails.eval a c7711 := derived7711 a h
  have h3 : Entails.eval a c7715 := derived7715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7721 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨46, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7721 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7209, some c7196, some c7198, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7721 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7721 : lratChecker f7721 p7721 = .success := by decide +kernel
theorem unsat7721 : Unsatisfiable (PosFin 65) f7721 := by
  apply lratCheckerSound f7721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7721
  · intro a ha; simp [p7721] at ha; subst a; trivial
  · exact checked7721
theorem derived7721 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7721 := by
  apply localUnsat_implies_entails f7721 [c7209, c7196, c7198] c7721 unsat7721 (by rfl) a
  have h0 : Entails.eval a c7209 := h 7208 (by decide)
  have h1 : Entails.eval a c7196 := h 7195 (by decide)
  have h2 : Entails.eval a c7198 := h 7197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7722 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7722 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7178, some c6817, some c6877, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7722 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7722 : lratChecker f7722 p7722 = .success := by decide +kernel
theorem unsat7722 : Unsatisfiable (PosFin 65) f7722 := by
  apply lratCheckerSound f7722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7722
  · intro a ha; simp [p7722] at ha; subst a; trivial
  · exact checked7722
theorem derived7722 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7722 := by
  apply localUnsat_implies_entails f7722 [c7178, c6817, c6877] c7722 unsat7722 (by rfl) a
  have h0 : Entails.eval a c7178 := h 7177 (by decide)
  have h1 : Entails.eval a c6817 := h 6816 (by decide)
  have h2 : Entails.eval a c6877 := h 6876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7723 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7723 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6815, some c7175, some c6874, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7723 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7723 : lratChecker f7723 p7723 = .success := by decide +kernel
theorem unsat7723 : Unsatisfiable (PosFin 65) f7723 := by
  apply lratCheckerSound f7723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7723
  · intro a ha; simp [p7723] at ha; subst a; trivial
  · exact checked7723
theorem derived7723 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7723 := by
  apply localUnsat_implies_entails f7723 [c6815, c7175, c6874] c7723 unsat7723 (by rfl) a
  have h0 : Entails.eval a c6815 := h 6814 (by decide)
  have h1 : Entails.eval a c7175 := h 7174 (by decide)
  have h2 : Entails.eval a c6874 := h 6873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7724 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7724 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7721, some c7722, some c7723, some c6822, some c7185, some c6886, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7724 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7724 : lratChecker f7724 p7724 = .success := by decide +kernel
theorem unsat7724 : Unsatisfiable (PosFin 65) f7724 := by
  apply lratCheckerSound f7724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7724
  · intro a ha; simp [p7724] at ha; subst a; trivial
  · exact checked7724
theorem derived7724 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7724 := by
  apply localUnsat_implies_entails f7724 [c7721, c7722, c7723, c6822, c7185, c6886] c7724 unsat7724 (by rfl) a
  have h0 : Entails.eval a c7721 := derived7721 a h
  have h1 : Entails.eval a c7722 := derived7722 a h
  have h2 : Entails.eval a c7723 := derived7723 a h
  have h3 : Entails.eval a c6822 := h 6821 (by decide)
  have h4 : Entails.eval a c7185 := h 7184 (by decide)
  have h5 : Entails.eval a c6886 := h 6885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7725 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7725 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6548, some c6512, some c6420, some c7358, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7725 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7725 : lratChecker f7725 p7725 = .success := by decide +kernel
theorem unsat7725 : Unsatisfiable (PosFin 65) f7725 := by
  apply lratCheckerSound f7725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7725
  · intro a ha; simp [p7725] at ha; subst a; trivial
  · exact checked7725
theorem derived7725 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7725 := by
  apply localUnsat_implies_entails f7725 [c6548, c6512, c6420, c7358] c7725 unsat7725 (by rfl) a
  have h0 : Entails.eval a c6548 := h 6547 (by decide)
  have h1 : Entails.eval a c6512 := h 6511 (by decide)
  have h2 : Entails.eval a c6420 := h 6419 (by decide)
  have h3 : Entails.eval a c7358 := h 7357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7726 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7726 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7720, some c7724, some c7718, some c7725, some c6422, some c6516, some c7136, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7726 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7726 : lratChecker f7726 p7726 = .success := by decide +kernel
theorem unsat7726 : Unsatisfiable (PosFin 65) f7726 := by
  apply lratCheckerSound f7726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7726
  · intro a ha; simp [p7726] at ha; subst a; trivial
  · exact checked7726
theorem derived7726 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7726 := by
  apply localUnsat_implies_entails f7726 [c7712, c7720, c7724, c7718, c7725, c6422, c6516, c7136] c7726 unsat7726 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7720 := derived7720 a h
  have h2 : Entails.eval a c7724 := derived7724 a h
  have h3 : Entails.eval a c7718 := derived7718 a h
  have h4 : Entails.eval a c7725 := derived7725 a h
  have h5 : Entails.eval a c6422 := h 6421 (by decide)
  have h6 : Entails.eval a c6516 := h 6515 (by decide)
  have h7 : Entails.eval a c7136 := h 7135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7727 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨45, by decide⟩, false), (⟨36, by decide⟩, false), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7727 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7087, some c7095, some c7029, some c7459, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p7727 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7727 : lratChecker f7727 p7727 = .success := by decide +kernel
theorem unsat7727 : Unsatisfiable (PosFin 65) f7727 := by
  apply lratCheckerSound f7727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7727
  · intro a ha; simp [p7727] at ha; subst a; trivial
  · exact checked7727
theorem derived7727 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7727 := by
  apply localUnsat_implies_entails f7727 [c7087, c7095, c7029, c7459] c7727 unsat7727 (by rfl) a
  have h0 : Entails.eval a c7087 := h 7086 (by decide)
  have h1 : Entails.eval a c7095 := h 7094 (by decide)
  have h2 : Entails.eval a c7029 := h 7028 (by decide)
  have h3 : Entails.eval a c7459 := h 7458 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7728 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨60, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7728 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6516, some c7727, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7728 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7728 : lratChecker f7728 p7728 = .success := by decide +kernel
theorem unsat7728 : Unsatisfiable (PosFin 65) f7728 := by
  apply lratCheckerSound f7728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7728
  · intro a ha; simp [p7728] at ha; subst a; trivial
  · exact checked7728
theorem derived7728 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7728 := by
  apply localUnsat_implies_entails f7728 [c6516, c7727] c7728 unsat7728 (by rfl) a
  have h0 : Entails.eval a c6516 := h 6515 (by decide)
  have h1 : Entails.eval a c7727 := derived7727 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7729 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7729 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6382, some c6429, some c6525, some c7364, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7729 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7729 : lratChecker f7729 p7729 = .success := by decide +kernel
theorem unsat7729 : Unsatisfiable (PosFin 65) f7729 := by
  apply lratCheckerSound f7729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7729
  · intro a ha; simp [p7729] at ha; subst a; trivial
  · exact checked7729
theorem derived7729 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7729 := by
  apply localUnsat_implies_entails f7729 [c6382, c6429, c6525, c7364] c7729 unsat7729 (by rfl) a
  have h0 : Entails.eval a c6382 := h 6381 (by decide)
  have h1 : Entails.eval a c6429 := h 6428 (by decide)
  have h2 : Entails.eval a c6525 := h 6524 (by decide)
  have h3 : Entails.eval a c7364 := h 7363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7730 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7730 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7726, some c7712, some c7729, some c7725, some c6423, some c6517, some c7088, some c7728, some c7363, some c7222, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7730 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7730 : lratChecker f7730 p7730 = .success := by decide +kernel
theorem unsat7730 : Unsatisfiable (PosFin 65) f7730 := by
  apply lratCheckerSound f7730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7730
  · intro a ha; simp [p7730] at ha; subst a; trivial
  · exact checked7730
theorem derived7730 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7730 := by
  apply localUnsat_implies_entails f7730 [c7726, c7712, c7729, c7725, c6423, c6517, c7088, c7728, c7363, c7222] c7730 unsat7730 (by rfl) a
  have h0 : Entails.eval a c7726 := derived7726 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c7729 := derived7729 a h
  have h3 : Entails.eval a c7725 := derived7725 a h
  have h4 : Entails.eval a c6423 := h 6422 (by decide)
  have h5 : Entails.eval a c6517 := h 6516 (by decide)
  have h6 : Entails.eval a c7088 := h 7087 (by decide)
  have h7 : Entails.eval a c7728 := derived7728 a h
  have h8 : Entails.eval a c7363 := h 7362 (by decide)
  have h9 : Entails.eval a c7222 := h 7221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7731 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7731 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6381, some c6383, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7731 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7731 : lratChecker f7731 p7731 = .success := by decide +kernel
theorem unsat7731 : Unsatisfiable (PosFin 65) f7731 := by
  apply lratCheckerSound f7731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7731
  · intro a ha; simp [p7731] at ha; subst a; trivial
  · exact checked7731
theorem derived7731 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7731 := by
  apply localUnsat_implies_entails f7731 [c6381, c6383] c7731 unsat7731 (by rfl) a
  have h0 : Entails.eval a c6381 := h 6380 (by decide)
  have h1 : Entails.eval a c6383 := h 6382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7732 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨43, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7732 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7238, some c7545, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7732 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7732 : lratChecker f7732 p7732 = .success := by decide +kernel
theorem unsat7732 : Unsatisfiable (PosFin 65) f7732 := by
  apply lratCheckerSound f7732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7732
  · intro a ha; simp [p7732] at ha; subst a; trivial
  · exact checked7732
theorem derived7732 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7732 := by
  apply localUnsat_implies_entails f7732 [c7238, c7545] c7732 unsat7732 (by rfl) a
  have h0 : Entails.eval a c7238 := h 7237 (by decide)
  have h1 : Entails.eval a c7545 := h 7544 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7733 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨50, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7733 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7678, some c6390, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7733 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7733 : lratChecker f7733 p7733 = .success := by decide +kernel
theorem unsat7733 : Unsatisfiable (PosFin 65) f7733 := by
  apply lratCheckerSound f7733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7733
  · intro a ha; simp [p7733] at ha; subst a; trivial
  · exact checked7733
theorem derived7733 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7733 := by
  apply localUnsat_implies_entails f7733 [c7678, c6390] c7733 unsat7733 (by rfl) a
  have h0 : Entails.eval a c7678 := derived7678 a h
  have h1 : Entails.eval a c6390 := h 6389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7734 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7734 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6362, some c7400, some c6851, some c6894, some c7030, some c6908, some c7733, some c7043, some c7425, some c7523, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7734 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7734 : lratChecker f7734 p7734 = .success := by decide +kernel
theorem unsat7734 : Unsatisfiable (PosFin 65) f7734 := by
  apply lratCheckerSound f7734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7734
  · intro a ha; simp [p7734] at ha; subst a; trivial
  · exact checked7734
theorem derived7734 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7734 := by
  apply localUnsat_implies_entails f7734 [c6362, c7400, c6851, c6894, c7030, c6908, c7733, c7043, c7425, c7523] c7734 unsat7734 (by rfl) a
  have h0 : Entails.eval a c6362 := h 6361 (by decide)
  have h1 : Entails.eval a c7400 := h 7399 (by decide)
  have h2 : Entails.eval a c6851 := h 6850 (by decide)
  have h3 : Entails.eval a c6894 := h 6893 (by decide)
  have h4 : Entails.eval a c7030 := h 7029 (by decide)
  have h5 : Entails.eval a c6908 := h 6907 (by decide)
  have h6 : Entails.eval a c7733 := derived7733 a h
  have h7 : Entails.eval a c7043 := h 7042 (by decide)
  have h8 : Entails.eval a c7425 := h 7424 (by decide)
  have h9 : Entails.eval a c7523 := h 7522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7735 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7735 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7041, some c7044, some c7050, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7735 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7735 : lratChecker f7735 p7735 = .success := by decide +kernel
theorem unsat7735 : Unsatisfiable (PosFin 65) f7735 := by
  apply lratCheckerSound f7735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7735
  · intro a ha; simp [p7735] at ha; subst a; trivial
  · exact checked7735
theorem derived7735 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7735 := by
  apply localUnsat_implies_entails f7735 [c7041, c7044, c7050] c7735 unsat7735 (by rfl) a
  have h0 : Entails.eval a c7041 := h 7040 (by decide)
  have h1 : Entails.eval a c7044 := h 7043 (by decide)
  have h2 : Entails.eval a c7050 := h 7049 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7736 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨17, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7736 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5505, some c5721, some c5294, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7736 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7736 : lratChecker f7736 p7736 = .success := by decide +kernel
theorem unsat7736 : Unsatisfiable (PosFin 65) f7736 := by
  apply lratCheckerSound f7736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7736
  · intro a ha; simp [p7736] at ha; subst a; trivial
  · exact checked7736
theorem derived7736 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7736 := by
  apply localUnsat_implies_entails f7736 [c5505, c5721, c5294] c7736 unsat7736 (by rfl) a
  have h0 : Entails.eval a c5505 := h 5504 (by decide)
  have h1 : Entails.eval a c5721 := h 5720 (by decide)
  have h2 : Entails.eval a c5294 := h 5293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7737 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨17, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7737 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7736, some c5204, some c5275, some c6007, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7737 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7737 : lratChecker f7737 p7737 = .success := by decide +kernel
theorem unsat7737 : Unsatisfiable (PosFin 65) f7737 := by
  apply lratCheckerSound f7737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7737
  · intro a ha; simp [p7737] at ha; subst a; trivial
  · exact checked7737
theorem derived7737 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7737 := by
  apply localUnsat_implies_entails f7737 [c7736, c5204, c5275, c6007] c7737 unsat7737 (by rfl) a
  have h0 : Entails.eval a c7736 := derived7736 a h
  have h1 : Entails.eval a c5204 := h 5203 (by decide)
  have h2 : Entails.eval a c5275 := h 5274 (by decide)
  have h3 : Entails.eval a c6007 := h 6006 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7738 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7738 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5624, some c6157, some c5301, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7738 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7738 : lratChecker f7738 p7738 = .success := by decide +kernel
theorem unsat7738 : Unsatisfiable (PosFin 65) f7738 := by
  apply lratCheckerSound f7738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7738
  · intro a ha; simp [p7738] at ha; subst a; trivial
  · exact checked7738
theorem derived7738 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7738 := by
  apply localUnsat_implies_entails f7738 [c5624, c6157, c5301] c7738 unsat7738 (by rfl) a
  have h0 : Entails.eval a c5624 := h 5623 (by decide)
  have h1 : Entails.eval a c6157 := h 6156 (by decide)
  have h2 : Entails.eval a c5301 := h 5300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7739 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7739 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7737, some c5235, some c5317, some c54, some c5284, some c6062, some c6189, some c5785, some c6044, some c7738, some c5661, some c42, some c6114, some c2930, some c2414, some c207, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7739 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7739 : lratChecker f7739 p7739 = .success := by decide +kernel
theorem unsat7739 : Unsatisfiable (PosFin 65) f7739 := by
  apply lratCheckerSound f7739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7739
  · intro a ha; simp [p7739] at ha; subst a; trivial
  · exact checked7739
theorem derived7739 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7739 := by
  apply localUnsat_implies_entails f7739 [c7737, c5235, c5317, c54, c5284, c6062, c6189, c5785, c6044, c7738, c5661, c42, c6114, c2930, c2414, c207] c7739 unsat7739 (by rfl) a
  have h0 : Entails.eval a c7737 := derived7737 a h
  have h1 : Entails.eval a c5235 := h 5234 (by decide)
  have h2 : Entails.eval a c5317 := h 5316 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c5284 := h 5283 (by decide)
  have h5 : Entails.eval a c6062 := h 6061 (by decide)
  have h6 : Entails.eval a c6189 := h 6188 (by decide)
  have h7 : Entails.eval a c5785 := h 5784 (by decide)
  have h8 : Entails.eval a c6044 := h 6043 (by decide)
  have h9 : Entails.eval a c7738 := derived7738 a h
  have h10 : Entails.eval a c5661 := h 5660 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c6114 := h 6113 (by decide)
  have h13 : Entails.eval a c2930 := h 2929 (by decide)
  have h14 : Entails.eval a c2414 := h 2413 (by decide)
  have h15 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7740 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨52, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7740 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5235, some c5284, some c6062, some c5392, some c5471, some c6030, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7740 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7740 : lratChecker f7740 p7740 = .success := by decide +kernel
theorem unsat7740 : Unsatisfiable (PosFin 65) f7740 := by
  apply lratCheckerSound f7740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7740
  · intro a ha; simp [p7740] at ha; subst a; trivial
  · exact checked7740
theorem derived7740 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7740 := by
  apply localUnsat_implies_entails f7740 [c5235, c5284, c6062, c5392, c5471, c6030] c7740 unsat7740 (by rfl) a
  have h0 : Entails.eval a c5235 := h 5234 (by decide)
  have h1 : Entails.eval a c5284 := h 5283 (by decide)
  have h2 : Entails.eval a c6062 := h 6061 (by decide)
  have h3 : Entails.eval a c5392 := h 5391 (by decide)
  have h4 : Entails.eval a c5471 := h 5470 (by decide)
  have h5 : Entails.eval a c6030 := h 6029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7741 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨21, by decide⟩, false), (⟨20, by decide⟩, true), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7741 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5257, some c6028, some c5917, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7741 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7741 : lratChecker f7741 p7741 = .success := by decide +kernel
theorem unsat7741 : Unsatisfiable (PosFin 65) f7741 := by
  apply lratCheckerSound f7741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7741
  · intro a ha; simp [p7741] at ha; subst a; trivial
  · exact checked7741
theorem derived7741 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7741 := by
  apply localUnsat_implies_entails f7741 [c5257, c6028, c5917] c7741 unsat7741 (by rfl) a
  have h0 : Entails.eval a c5257 := h 5256 (by decide)
  have h1 : Entails.eval a c6028 := h 6027 (by decide)
  have h2 : Entails.eval a c5917 := h 5916 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7742 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7742 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7741, some c5367, some c5380, some c6044, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7742 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7742 : lratChecker f7742 p7742 = .success := by decide +kernel
theorem unsat7742 : Unsatisfiable (PosFin 65) f7742 := by
  apply lratCheckerSound f7742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7742
  · intro a ha; simp [p7742] at ha; subst a; trivial
  · exact checked7742
theorem derived7742 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7742 := by
  apply localUnsat_implies_entails f7742 [c7741, c5367, c5380, c6044] c7742 unsat7742 (by rfl) a
  have h0 : Entails.eval a c7741 := derived7741 a h
  have h1 : Entails.eval a c5367 := h 5366 (by decide)
  have h2 : Entails.eval a c5380 := h 5379 (by decide)
  have h3 : Entails.eval a c6044 := h 6043 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7743 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨60, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7743 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7726, some c7730, some c7734, some c7735, some c6382, some c6414, some c6664, some c6636, some c7515, some c7680, some c7364, some c6600, some c7424, some c7428, some c7279, some c7739, some c7740, some c7742, some c5348, some c5359, some c5262, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7743 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked7743 : lratChecker f7743 p7743 = .success := by decide +kernel
theorem unsat7743 : Unsatisfiable (PosFin 65) f7743 := by
  apply lratCheckerSound f7743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7743
  · intro a ha; simp [p7743] at ha; subst a; trivial
  · exact checked7743
theorem derived7743 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7743 := by
  apply localUnsat_implies_entails f7743 [c7712, c7726, c7730, c7734, c7735, c6382, c6414, c6664, c6636, c7515, c7680, c7364, c6600, c7424, c7428, c7279, c7739, c7740, c7742, c5348, c5359, c5262] c7743 unsat7743 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7726 := derived7726 a h
  have h2 : Entails.eval a c7730 := derived7730 a h
  have h3 : Entails.eval a c7734 := derived7734 a h
  have h4 : Entails.eval a c7735 := derived7735 a h
  have h5 : Entails.eval a c6382 := h 6381 (by decide)
  have h6 : Entails.eval a c6414 := h 6413 (by decide)
  have h7 : Entails.eval a c6664 := h 6663 (by decide)
  have h8 : Entails.eval a c6636 := h 6635 (by decide)
  have h9 : Entails.eval a c7515 := h 7514 (by decide)
  have h10 : Entails.eval a c7680 := derived7680 a h
  have h11 : Entails.eval a c7364 := h 7363 (by decide)
  have h12 : Entails.eval a c6600 := h 6599 (by decide)
  have h13 : Entails.eval a c7424 := h 7423 (by decide)
  have h14 : Entails.eval a c7428 := h 7427 (by decide)
  have h15 : Entails.eval a c7279 := h 7278 (by decide)
  have h16 : Entails.eval a c7739 := derived7739 a h
  have h17 : Entails.eval a c7740 := derived7740 a h
  have h18 : Entails.eval a c7742 := derived7742 a h
  have h19 : Entails.eval a c5348 := h 5347 (by decide)
  have h20 : Entails.eval a c5359 := h 5358 (by decide)
  have h21 : Entails.eval a c5262 := h 5261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7744 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7744 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5349, some c5360, some c5262, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7744 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7744 : lratChecker f7744 p7744 = .success := by decide +kernel
theorem unsat7744 : Unsatisfiable (PosFin 65) f7744 := by
  apply lratCheckerSound f7744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7744
  · intro a ha; simp [p7744] at ha; subst a; trivial
  · exact checked7744
theorem derived7744 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7744 := by
  apply localUnsat_implies_entails f7744 [c5349, c5360, c5262] c7744 unsat7744 (by rfl) a
  have h0 : Entails.eval a c5349 := h 5348 (by decide)
  have h1 : Entails.eval a c5360 := h 5359 (by decide)
  have h2 : Entails.eval a c5262 := h 5261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7745 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7745 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7364, some c6664, some c6600, some c5207, some c5257, some c5713, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7745 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7745 : lratChecker f7745 p7745 = .success := by decide +kernel
theorem unsat7745 : Unsatisfiable (PosFin 65) f7745 := by
  apply lratCheckerSound f7745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7745
  · intro a ha; simp [p7745] at ha; subst a; trivial
  · exact checked7745
theorem derived7745 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7745 := by
  apply localUnsat_implies_entails f7745 [c7364, c6664, c6600, c5207, c5257, c5713] c7745 unsat7745 (by rfl) a
  have h0 : Entails.eval a c7364 := h 7363 (by decide)
  have h1 : Entails.eval a c6664 := h 6663 (by decide)
  have h2 : Entails.eval a c6600 := h 6599 (by decide)
  have h3 : Entails.eval a c5207 := h 5206 (by decide)
  have h4 : Entails.eval a c5257 := h 5256 (by decide)
  have h5 : Entails.eval a c5713 := h 5712 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7746 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨46, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7746 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7364, some c6664, some c6600, some c7745, some c5918, some c6025, some c6047, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7746 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7746 : lratChecker f7746 p7746 = .success := by decide +kernel
theorem unsat7746 : Unsatisfiable (PosFin 65) f7746 := by
  apply lratCheckerSound f7746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7746
  · intro a ha; simp [p7746] at ha; subst a; trivial
  · exact checked7746
theorem derived7746 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7746 := by
  apply localUnsat_implies_entails f7746 [c7364, c6664, c6600, c7745, c5918, c6025, c6047] c7746 unsat7746 (by rfl) a
  have h0 : Entails.eval a c7364 := h 7363 (by decide)
  have h1 : Entails.eval a c6664 := h 6663 (by decide)
  have h2 : Entails.eval a c6600 := h 6599 (by decide)
  have h3 : Entails.eval a c7745 := derived7745 a h
  have h4 : Entails.eval a c5918 := h 5917 (by decide)
  have h5 : Entails.eval a c6025 := h 6024 (by decide)
  have h6 : Entails.eval a c6047 := h 6046 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7747 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨39, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨38, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7747 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6382, some c7364, some c6664, some c6600, some c7744, some c7746, some c5281, some c5393, some c5472, some c6031, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7747 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7747 : lratChecker f7747 p7747 = .success := by decide +kernel
theorem unsat7747 : Unsatisfiable (PosFin 65) f7747 := by
  apply lratCheckerSound f7747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7747
  · intro a ha; simp [p7747] at ha; subst a; trivial
  · exact checked7747
theorem derived7747 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7747 := by
  apply localUnsat_implies_entails f7747 [c6382, c7364, c6664, c6600, c7744, c7746, c5281, c5393, c5472, c6031] c7747 unsat7747 (by rfl) a
  have h0 : Entails.eval a c6382 := h 6381 (by decide)
  have h1 : Entails.eval a c7364 := h 7363 (by decide)
  have h2 : Entails.eval a c6664 := h 6663 (by decide)
  have h3 : Entails.eval a c6600 := h 6599 (by decide)
  have h4 : Entails.eval a c7744 := derived7744 a h
  have h5 : Entails.eval a c7746 := derived7746 a h
  have h6 : Entails.eval a c5281 := h 5280 (by decide)
  have h7 : Entails.eval a c5393 := h 5392 (by decide)
  have h8 : Entails.eval a c5472 := h 5471 (by decide)
  have h9 : Entails.eval a c6031 := h 6030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7748 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨39, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7748 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6382, some c6414, some c7364, some c6664, some c6600, some c6636, some c5235, some c5317, some c54, some c5281, some c5787, some c5204, some c42, some c6115, some c2940, some c67, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7748 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7748 : lratChecker f7748 p7748 = .success := by decide +kernel
theorem unsat7748 : Unsatisfiable (PosFin 65) f7748 := by
  apply lratCheckerSound f7748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7748
  · intro a ha; simp [p7748] at ha; subst a; trivial
  · exact checked7748
theorem derived7748 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7748 := by
  apply localUnsat_implies_entails f7748 [c6382, c6414, c7364, c6664, c6600, c6636, c5235, c5317, c54, c5281, c5787, c5204, c42, c6115, c2940, c67] c7748 unsat7748 (by rfl) a
  have h0 : Entails.eval a c6382 := h 6381 (by decide)
  have h1 : Entails.eval a c6414 := h 6413 (by decide)
  have h2 : Entails.eval a c7364 := h 7363 (by decide)
  have h3 : Entails.eval a c6664 := h 6663 (by decide)
  have h4 : Entails.eval a c6600 := h 6599 (by decide)
  have h5 : Entails.eval a c6636 := h 6635 (by decide)
  have h6 : Entails.eval a c5235 := h 5234 (by decide)
  have h7 : Entails.eval a c5317 := h 5316 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c5281 := h 5280 (by decide)
  have h10 : Entails.eval a c5787 := h 5786 (by decide)
  have h11 : Entails.eval a c5204 := h 5203 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c6115 := h 6114 (by decide)
  have h14 : Entails.eval a c2940 := h 2939 (by decide)
  have h15 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7749 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7749 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7726, some c6382, some c7712, some c7730, some c7734, some c7735, some c6414, some c7364, some c6664, some c6600, some c6936, some c6636, some c7515, some c7680, some c7743, some c7378, some c6450, some c7397, some c6678, some c7747, some c7748, some c7745, some c7746, some c5839, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7749 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked7749 : lratChecker f7749 p7749 = .success := by decide +kernel
theorem unsat7749 : Unsatisfiable (PosFin 65) f7749 := by
  apply lratCheckerSound f7749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7749
  · intro a ha; simp [p7749] at ha; subst a; trivial
  · exact checked7749
theorem derived7749 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7749 := by
  apply localUnsat_implies_entails f7749 [c7726, c6382, c7712, c7730, c7734, c7735, c6414, c7364, c6664, c6600, c6936, c6636, c7515, c7680, c7743, c7378, c6450, c7397, c6678, c7747, c7748, c7745, c7746, c5839] c7749 unsat7749 (by rfl) a
  have h0 : Entails.eval a c7726 := derived7726 a h
  have h1 : Entails.eval a c6382 := h 6381 (by decide)
  have h2 : Entails.eval a c7712 := derived7712 a h
  have h3 : Entails.eval a c7730 := derived7730 a h
  have h4 : Entails.eval a c7734 := derived7734 a h
  have h5 : Entails.eval a c7735 := derived7735 a h
  have h6 : Entails.eval a c6414 := h 6413 (by decide)
  have h7 : Entails.eval a c7364 := h 7363 (by decide)
  have h8 : Entails.eval a c6664 := h 6663 (by decide)
  have h9 : Entails.eval a c6600 := h 6599 (by decide)
  have h10 : Entails.eval a c6936 := h 6935 (by decide)
  have h11 : Entails.eval a c6636 := h 6635 (by decide)
  have h12 : Entails.eval a c7515 := h 7514 (by decide)
  have h13 : Entails.eval a c7680 := derived7680 a h
  have h14 : Entails.eval a c7743 := derived7743 a h
  have h15 : Entails.eval a c7378 := h 7377 (by decide)
  have h16 : Entails.eval a c6450 := h 6449 (by decide)
  have h17 : Entails.eval a c7397 := h 7396 (by decide)
  have h18 : Entails.eval a c6678 := h 6677 (by decide)
  have h19 : Entails.eval a c7747 := derived7747 a h
  have h20 : Entails.eval a c7748 := derived7748 a h
  have h21 : Entails.eval a c7745 := derived7745 a h
  have h22 : Entails.eval a c7746 := derived7746 a h
  have h23 : Entails.eval a c5839 := h 5838 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7750 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7750 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7726, some c6382, some c7712, some c7730, some c7734, some c7735, some c6414, some c6664, some c6636, some c7364, some c7749, some c7401, some c6465, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7750 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7750 : lratChecker f7750 p7750 = .success := by decide +kernel
theorem unsat7750 : Unsatisfiable (PosFin 65) f7750 := by
  apply lratCheckerSound f7750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7750
  · intro a ha; simp [p7750] at ha; subst a; trivial
  · exact checked7750
theorem derived7750 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7750 := by
  apply localUnsat_implies_entails f7750 [c7726, c6382, c7712, c7730, c7734, c7735, c6414, c6664, c6636, c7364, c7749, c7401, c6465] c7750 unsat7750 (by rfl) a
  have h0 : Entails.eval a c7726 := derived7726 a h
  have h1 : Entails.eval a c6382 := h 6381 (by decide)
  have h2 : Entails.eval a c7712 := derived7712 a h
  have h3 : Entails.eval a c7730 := derived7730 a h
  have h4 : Entails.eval a c7734 := derived7734 a h
  have h5 : Entails.eval a c7735 := derived7735 a h
  have h6 : Entails.eval a c6414 := h 6413 (by decide)
  have h7 : Entails.eval a c6664 := h 6663 (by decide)
  have h8 : Entails.eval a c6636 := h 6635 (by decide)
  have h9 : Entails.eval a c7364 := h 7363 (by decide)
  have h10 : Entails.eval a c7749 := derived7749 a h
  have h11 : Entails.eval a c7401 := h 7400 (by decide)
  have h12 : Entails.eval a c6465 := h 6464 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7750

end CochromaticTwenty.Certificates.FixedCore0
