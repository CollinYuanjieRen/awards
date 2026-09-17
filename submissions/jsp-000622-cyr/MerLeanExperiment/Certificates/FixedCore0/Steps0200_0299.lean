import MerLeanExperiment.Certificates.FixedCore0.Steps0100_0199

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7751 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7751 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7726, some c7730, some c7734, some c7735, some c6382, some c6414, some c7364, some c6664, some c6636, some c6600, some c7533, some c6936, some c7750, some c7408, some c6995, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7751 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7751 : lratChecker f7751 p7751 = .success := by decide +kernel
theorem unsat7751 : Unsatisfiable (PosFin 65) f7751 := by
  apply lratCheckerSound f7751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7751
  · intro a ha; simp [p7751] at ha; subst a; trivial
  · exact checked7751
theorem derived7751 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7751 := by
  apply localUnsat_implies_entails f7751 [c7712, c7726, c7730, c7734, c7735, c6382, c6414, c7364, c6664, c6636, c6600, c7533, c6936, c7750, c7408, c6995] c7751 unsat7751 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7726 := derived7726 a h
  have h2 : Entails.eval a c7730 := derived7730 a h
  have h3 : Entails.eval a c7734 := derived7734 a h
  have h4 : Entails.eval a c7735 := derived7735 a h
  have h5 : Entails.eval a c6382 := h 6381 (by decide)
  have h6 : Entails.eval a c6414 := h 6413 (by decide)
  have h7 : Entails.eval a c7364 := h 7363 (by decide)
  have h8 : Entails.eval a c6664 := h 6663 (by decide)
  have h9 : Entails.eval a c6636 := h 6635 (by decide)
  have h10 : Entails.eval a c6600 := h 6599 (by decide)
  have h11 : Entails.eval a c7533 := h 7532 (by decide)
  have h12 : Entails.eval a c6936 := h 6935 (by decide)
  have h13 : Entails.eval a c7750 := derived7750 a h
  have h14 : Entails.eval a c7408 := h 7407 (by decide)
  have h15 : Entails.eval a c6995 := h 6994 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7752 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨42, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, false), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7752 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7408, some c6995, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7752 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7752 : lratChecker f7752 p7752 = .success := by decide +kernel
theorem unsat7752 : Unsatisfiable (PosFin 65) f7752 := by
  apply lratCheckerSound f7752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7752
  · intro a ha; simp [p7752] at ha; subst a; trivial
  · exact checked7752
theorem derived7752 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7752 := by
  apply localUnsat_implies_entails f7752 [c7408, c6995] c7752 unsat7752 (by rfl) a
  have h0 : Entails.eval a c7408 := h 7407 (by decide)
  have h1 : Entails.eval a c6995 := h 6994 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7753 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨62, by decide⟩, false), (⟨35, by decide⟩, false), (⟨46, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7753 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5831, some c5839, some c5568, some c5679, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p7753 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7753 : lratChecker f7753 p7753 = .success := by decide +kernel
theorem unsat7753 : Unsatisfiable (PosFin 65) f7753 := by
  apply lratCheckerSound f7753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7753
  · intro a ha; simp [p7753] at ha; subst a; trivial
  · exact checked7753
theorem derived7753 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7753 := by
  apply localUnsat_implies_entails f7753 [c5831, c5839, c5568, c5679] c7753 unsat7753 (by rfl) a
  have h0 : Entails.eval a c5831 := h 5830 (by decide)
  have h1 : Entails.eval a c5839 := h 5838 (by decide)
  have h2 : Entails.eval a c5568 := h 5567 (by decide)
  have h3 : Entails.eval a c5679 := h 5678 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7754 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨35, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7754 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5205, some c5256, some c5712, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7754 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7754 : lratChecker f7754 p7754 = .success := by decide +kernel
theorem unsat7754 : Unsatisfiable (PosFin 65) f7754 := by
  apply lratCheckerSound f7754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7754
  · intro a ha; simp [p7754] at ha; subst a; trivial
  · exact checked7754
theorem derived7754 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7754 := by
  apply localUnsat_implies_entails f7754 [c5205, c5256, c5712] c7754 unsat7754 (by rfl) a
  have h0 : Entails.eval a c5205 := h 5204 (by decide)
  have h1 : Entails.eval a c5256 := h 5255 (by decide)
  have h2 : Entails.eval a c5712 := h 5711 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7755 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨46, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7755 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7753, some c7754, some c5918, some c6010, some c6047, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7755 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7755 : lratChecker f7755 p7755 = .success := by decide +kernel
theorem unsat7755 : Unsatisfiable (PosFin 65) f7755 := by
  apply lratCheckerSound f7755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7755
  · intro a ha; simp [p7755] at ha; subst a; trivial
  · exact checked7755
theorem derived7755 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7755 := by
  apply localUnsat_implies_entails f7755 [c7753, c7754, c5918, c6010, c6047] c7755 unsat7755 (by rfl) a
  have h0 : Entails.eval a c7753 := derived7753 a h
  have h1 : Entails.eval a c7754 := derived7754 a h
  have h2 : Entails.eval a c5918 := h 5917 (by decide)
  have h3 : Entails.eval a c6010 := h 6009 (by decide)
  have h4 : Entails.eval a c6047 := h 6046 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7756 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7756 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7726, some c7730, some c7734, some c7751, some c7102, some c7735, some c7458, some c7530, some c7752, some c7522, some c6874, some c6405, some c6371, some c7424, some c7265, some c7014, some c7282, some c7281, some c6864, some c7279, some c7432, some c7755, some c52, some c5234, some c5284, some c5794, some c41, some c2939, some c2997, some c2414, some c2616, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7756 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked7756 : lratChecker f7756 p7756 = .success := by decide +kernel
theorem unsat7756 : Unsatisfiable (PosFin 65) f7756 := by
  apply lratCheckerSound f7756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7756
  · intro a ha; simp [p7756] at ha; subst a; trivial
  · exact checked7756
theorem derived7756 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7756 := by
  apply localUnsat_implies_entails f7756 [c7712, c7726, c7730, c7734, c7751, c7102, c7735, c7458, c7530, c7752, c7522, c6874, c6405, c6371, c7424, c7265, c7014, c7282, c7281, c6864, c7279, c7432, c7755, c52, c5234, c5284, c5794, c41, c2939, c2997, c2414, c2616] c7756 unsat7756 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7726 := derived7726 a h
  have h2 : Entails.eval a c7730 := derived7730 a h
  have h3 : Entails.eval a c7734 := derived7734 a h
  have h4 : Entails.eval a c7751 := derived7751 a h
  have h5 : Entails.eval a c7102 := h 7101 (by decide)
  have h6 : Entails.eval a c7735 := derived7735 a h
  have h7 : Entails.eval a c7458 := h 7457 (by decide)
  have h8 : Entails.eval a c7530 := h 7529 (by decide)
  have h9 : Entails.eval a c7752 := derived7752 a h
  have h10 : Entails.eval a c7522 := h 7521 (by decide)
  have h11 : Entails.eval a c6874 := h 6873 (by decide)
  have h12 : Entails.eval a c6405 := h 6404 (by decide)
  have h13 : Entails.eval a c6371 := h 6370 (by decide)
  have h14 : Entails.eval a c7424 := h 7423 (by decide)
  have h15 : Entails.eval a c7265 := h 7264 (by decide)
  have h16 : Entails.eval a c7014 := h 7013 (by decide)
  have h17 : Entails.eval a c7282 := h 7281 (by decide)
  have h18 : Entails.eval a c7281 := h 7280 (by decide)
  have h19 : Entails.eval a c6864 := h 6863 (by decide)
  have h20 : Entails.eval a c7279 := h 7278 (by decide)
  have h21 : Entails.eval a c7432 := h 7431 (by decide)
  have h22 : Entails.eval a c7755 := derived7755 a h
  have h23 : Entails.eval a c52 := h 51 (by decide)
  have h24 : Entails.eval a c5234 := h 5233 (by decide)
  have h25 : Entails.eval a c5284 := h 5283 (by decide)
  have h26 : Entails.eval a c5794 := h 5793 (by decide)
  have h27 : Entails.eval a c41 := h 40 (by decide)
  have h28 : Entails.eval a c2939 := h 2938 (by decide)
  have h29 : Entails.eval a c2997 := h 2996 (by decide)
  have h30 : Entails.eval a c2414 := h 2413 (by decide)
  have h31 : Entails.eval a c2616 := h 2615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7757 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7757 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7726, some c7730, some c7734, some c7712, some c7735, some c7751, some c6371, some c7102, some c7522, some c7458, some c6405, some c6874, some c7358, some c7530, some c7752, some c7756, some c7378, some c6448, some c6363, some c7414, some c6763, some c6675, some c7146, some c7755, some c52, some c5234, some c5281, some c5787, some c41, some c2940, some c2998, some c2416, some c2616, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7757 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked7757 : lratChecker f7757 p7757 = .success := by decide +kernel
theorem unsat7757 : Unsatisfiable (PosFin 65) f7757 := by
  apply lratCheckerSound f7757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7757
  · intro a ha; simp [p7757] at ha; subst a; trivial
  · exact checked7757
theorem derived7757 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7757 := by
  apply localUnsat_implies_entails f7757 [c7726, c7730, c7734, c7712, c7735, c7751, c6371, c7102, c7522, c7458, c6405, c6874, c7358, c7530, c7752, c7756, c7378, c6448, c6363, c7414, c6763, c6675, c7146, c7755, c52, c5234, c5281, c5787, c41, c2940, c2998, c2416, c2616] c7757 unsat7757 (by rfl) a
  have h0 : Entails.eval a c7726 := derived7726 a h
  have h1 : Entails.eval a c7730 := derived7730 a h
  have h2 : Entails.eval a c7734 := derived7734 a h
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c7735 := derived7735 a h
  have h5 : Entails.eval a c7751 := derived7751 a h
  have h6 : Entails.eval a c6371 := h 6370 (by decide)
  have h7 : Entails.eval a c7102 := h 7101 (by decide)
  have h8 : Entails.eval a c7522 := h 7521 (by decide)
  have h9 : Entails.eval a c7458 := h 7457 (by decide)
  have h10 : Entails.eval a c6405 := h 6404 (by decide)
  have h11 : Entails.eval a c6874 := h 6873 (by decide)
  have h12 : Entails.eval a c7358 := h 7357 (by decide)
  have h13 : Entails.eval a c7530 := h 7529 (by decide)
  have h14 : Entails.eval a c7752 := derived7752 a h
  have h15 : Entails.eval a c7756 := derived7756 a h
  have h16 : Entails.eval a c7378 := h 7377 (by decide)
  have h17 : Entails.eval a c6448 := h 6447 (by decide)
  have h18 : Entails.eval a c6363 := h 6362 (by decide)
  have h19 : Entails.eval a c7414 := h 7413 (by decide)
  have h20 : Entails.eval a c6763 := h 6762 (by decide)
  have h21 : Entails.eval a c6675 := h 6674 (by decide)
  have h22 : Entails.eval a c7146 := h 7145 (by decide)
  have h23 : Entails.eval a c7755 := derived7755 a h
  have h24 : Entails.eval a c52 := h 51 (by decide)
  have h25 : Entails.eval a c5234 := h 5233 (by decide)
  have h26 : Entails.eval a c5281 := h 5280 (by decide)
  have h27 : Entails.eval a c5787 := h 5786 (by decide)
  have h28 : Entails.eval a c41 := h 40 (by decide)
  have h29 : Entails.eval a c2940 := h 2939 (by decide)
  have h30 : Entails.eval a c2998 := h 2997 (by decide)
  have h31 : Entails.eval a c2416 := h 2415 (by decide)
  have h32 : Entails.eval a c2616 := h 2615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7758 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7758 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7726, some c7730, some c7734, some c7757, some c6386, some c7678, some c6393, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7758 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7758 : lratChecker f7758 p7758 = .success := by decide +kernel
theorem unsat7758 : Unsatisfiable (PosFin 65) f7758 := by
  apply lratCheckerSound f7758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7758
  · intro a ha; simp [p7758] at ha; subst a; trivial
  · exact checked7758
theorem derived7758 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7758 := by
  apply localUnsat_implies_entails f7758 [c7712, c7726, c7730, c7734, c7757, c6386, c7678, c6393] c7758 unsat7758 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7726 := derived7726 a h
  have h2 : Entails.eval a c7730 := derived7730 a h
  have h3 : Entails.eval a c7734 := derived7734 a h
  have h4 : Entails.eval a c7757 := derived7757 a h
  have h5 : Entails.eval a c6386 := h 6385 (by decide)
  have h6 : Entails.eval a c7678 := derived7678 a h
  have h7 : Entails.eval a c6393 := h 6392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7759 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7759 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6350, some c6334, some c6716, some c6276, some c7462, some c7032, some c6914, some c7393, some c5160, some c5228, some c5212, some c5425, some c5409, some c5404, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7759 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7759 : lratChecker f7759 p7759 = .success := by decide +kernel
theorem unsat7759 : Unsatisfiable (PosFin 65) f7759 := by
  apply lratCheckerSound f7759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7759
  · intro a ha; simp [p7759] at ha; subst a; trivial
  · exact checked7759
theorem derived7759 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7759 := by
  apply localUnsat_implies_entails f7759 [c6350, c6334, c6716, c6276, c7462, c7032, c6914, c7393, c5160, c5228, c5212, c5425, c5409, c5404] c7759 unsat7759 (by rfl) a
  have h0 : Entails.eval a c6350 := h 6349 (by decide)
  have h1 : Entails.eval a c6334 := h 6333 (by decide)
  have h2 : Entails.eval a c6716 := h 6715 (by decide)
  have h3 : Entails.eval a c6276 := h 6275 (by decide)
  have h4 : Entails.eval a c7462 := h 7461 (by decide)
  have h5 : Entails.eval a c7032 := h 7031 (by decide)
  have h6 : Entails.eval a c6914 := h 6913 (by decide)
  have h7 : Entails.eval a c7393 := h 7392 (by decide)
  have h8 : Entails.eval a c5160 := h 5159 (by decide)
  have h9 : Entails.eval a c5228 := h 5227 (by decide)
  have h10 : Entails.eval a c5212 := h 5211 (by decide)
  have h11 : Entails.eval a c5425 := h 5424 (by decide)
  have h12 : Entails.eval a c5409 := h 5408 (by decide)
  have h13 : Entails.eval a c5404 := h 5403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7760 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7760 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6350, some c6334, some c6716, some c6276, some c7462, some c7032, some c7393, some c6914, some c7759, some c7649, some c5145, some c5184, some c5334, some c5188, some c5197, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7760 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7760 : lratChecker f7760 p7760 = .success := by decide +kernel
theorem unsat7760 : Unsatisfiable (PosFin 65) f7760 := by
  apply lratCheckerSound f7760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7760
  · intro a ha; simp [p7760] at ha; subst a; trivial
  · exact checked7760
theorem derived7760 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7760 := by
  apply localUnsat_implies_entails f7760 [c6350, c6334, c6716, c6276, c7462, c7032, c7393, c6914, c7759, c7649, c5145, c5184, c5334, c5188, c5197] c7760 unsat7760 (by rfl) a
  have h0 : Entails.eval a c6350 := h 6349 (by decide)
  have h1 : Entails.eval a c6334 := h 6333 (by decide)
  have h2 : Entails.eval a c6716 := h 6715 (by decide)
  have h3 : Entails.eval a c6276 := h 6275 (by decide)
  have h4 : Entails.eval a c7462 := h 7461 (by decide)
  have h5 : Entails.eval a c7032 := h 7031 (by decide)
  have h6 : Entails.eval a c7393 := h 7392 (by decide)
  have h7 : Entails.eval a c6914 := h 6913 (by decide)
  have h8 : Entails.eval a c7759 := derived7759 a h
  have h9 : Entails.eval a c7649 := derived7649 a h
  have h10 : Entails.eval a c5145 := h 5144 (by decide)
  have h11 : Entails.eval a c5184 := h 5183 (by decide)
  have h12 : Entails.eval a c5334 := h 5333 (by decide)
  have h13 : Entails.eval a c5188 := h 5187 (by decide)
  have h14 : Entails.eval a c5197 := h 5196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7761 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨58, by decide⟩, false), (⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7761 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5252, some c5197, some c5704, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7761 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7761 : lratChecker f7761 p7761 = .success := by decide +kernel
theorem unsat7761 : Unsatisfiable (PosFin 65) f7761 := by
  apply lratCheckerSound f7761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7761
  · intro a ha; simp [p7761] at ha; subst a; trivial
  · exact checked7761
theorem derived7761 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7761 := by
  apply localUnsat_implies_entails f7761 [c5252, c5197, c5704] c7761 unsat7761 (by rfl) a
  have h0 : Entails.eval a c5252 := h 5251 (by decide)
  have h1 : Entails.eval a c5197 := h 5196 (by decide)
  have h2 : Entails.eval a c5704 := h 5703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7762 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7762 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5344, some c5434, some c5415, some c6042, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7762 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7762 : lratChecker f7762 p7762 = .success := by decide +kernel
theorem unsat7762 : Unsatisfiable (PosFin 65) f7762 := by
  apply lratCheckerSound f7762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7762
  · intro a ha; simp [p7762] at ha; subst a; trivial
  · exact checked7762
theorem derived7762 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7762 := by
  apply localUnsat_implies_entails f7762 [c5344, c5434, c5415, c6042] c7762 unsat7762 (by rfl) a
  have h0 : Entails.eval a c5344 := h 5343 (by decide)
  have h1 : Entails.eval a c5434 := h 5433 (by decide)
  have h2 : Entails.eval a c5415 := h 5414 (by decide)
  have h3 : Entails.eval a c6042 := h 6041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7763 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7763 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7761, some c7762, some c5139, some c5127, some c5536, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7763 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7763 : lratChecker f7763 p7763 = .success := by decide +kernel
theorem unsat7763 : Unsatisfiable (PosFin 65) f7763 := by
  apply lratCheckerSound f7763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7763
  · intro a ha; simp [p7763] at ha; subst a; trivial
  · exact checked7763
theorem derived7763 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7763 := by
  apply localUnsat_implies_entails f7763 [c7761, c7762, c5139, c5127, c5536] c7763 unsat7763 (by rfl) a
  have h0 : Entails.eval a c7761 := derived7761 a h
  have h1 : Entails.eval a c7762 := derived7762 a h
  have h2 : Entails.eval a c5139 := h 5138 (by decide)
  have h3 : Entails.eval a c5127 := h 5126 (by decide)
  have h4 : Entails.eval a c5536 := h 5535 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7764 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7764 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5139, some c5127, some c5534, some c5528, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7764 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7764 : lratChecker f7764 p7764 = .success := by decide +kernel
theorem unsat7764 : Unsatisfiable (PosFin 65) f7764 := by
  apply lratCheckerSound f7764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7764
  · intro a ha; simp [p7764] at ha; subst a; trivial
  · exact checked7764
theorem derived7764 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7764 := by
  apply localUnsat_implies_entails f7764 [c5139, c5127, c5534, c5528] c7764 unsat7764 (by rfl) a
  have h0 : Entails.eval a c5139 := h 5138 (by decide)
  have h1 : Entails.eval a c5127 := h 5126 (by decide)
  have h2 : Entails.eval a c5534 := h 5533 (by decide)
  have h3 : Entails.eval a c5528 := h 5527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7765 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨58, by decide⟩, true), (⟨60, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7765 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5327, some c5431, some c5410, some c6042, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7765 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7765 : lratChecker f7765 p7765 = .success := by decide +kernel
theorem unsat7765 : Unsatisfiable (PosFin 65) f7765 := by
  apply lratCheckerSound f7765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7765
  · intro a ha; simp [p7765] at ha; subst a; trivial
  · exact checked7765
theorem derived7765 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7765 := by
  apply localUnsat_implies_entails f7765 [c5327, c5431, c5410, c6042] c7765 unsat7765 (by rfl) a
  have h0 : Entails.eval a c5327 := h 5326 (by decide)
  have h1 : Entails.eval a c5431 := h 5430 (by decide)
  have h2 : Entails.eval a c5410 := h 5409 (by decide)
  have h3 : Entails.eval a c6042 := h 6041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7766 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7766 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7763, some c7764, some c7765, some c5252, some c5188, some c5704, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7766 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7766 : lratChecker f7766 p7766 = .success := by decide +kernel
theorem unsat7766 : Unsatisfiable (PosFin 65) f7766 := by
  apply lratCheckerSound f7766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7766
  · intro a ha; simp [p7766] at ha; subst a; trivial
  · exact checked7766
theorem derived7766 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7766 := by
  apply localUnsat_implies_entails f7766 [c7763, c7764, c7765, c5252, c5188, c5704] c7766 unsat7766 (by rfl) a
  have h0 : Entails.eval a c7763 := derived7763 a h
  have h1 : Entails.eval a c7764 := derived7764 a h
  have h2 : Entails.eval a c7765 := derived7765 a h
  have h3 : Entails.eval a c5252 := h 5251 (by decide)
  have h4 : Entails.eval a c5188 := h 5187 (by decide)
  have h5 : Entails.eval a c5704 := h 5703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7767 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7767 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7758, some c7712, some c6350, some c6334, some c7462, some c6716, some c7236, some c7032, some c6276, some c7180, some c7393, some c7327, some c7760, some c6948, some c7766, some c5153, some c5223, some c5212, some c5415, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7767 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7767 : lratChecker f7767 p7767 = .success := by decide +kernel
theorem unsat7767 : Unsatisfiable (PosFin 65) f7767 := by
  apply lratCheckerSound f7767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7767
  · intro a ha; simp [p7767] at ha; subst a; trivial
  · exact checked7767
theorem derived7767 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7767 := by
  apply localUnsat_implies_entails f7767 [c7758, c7712, c6350, c6334, c7462, c6716, c7236, c7032, c6276, c7180, c7393, c7327, c7760, c6948, c7766, c5153, c5223, c5212, c5415] c7767 unsat7767 (by rfl) a
  have h0 : Entails.eval a c7758 := derived7758 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c6350 := h 6349 (by decide)
  have h3 : Entails.eval a c6334 := h 6333 (by decide)
  have h4 : Entails.eval a c7462 := h 7461 (by decide)
  have h5 : Entails.eval a c6716 := h 6715 (by decide)
  have h6 : Entails.eval a c7236 := h 7235 (by decide)
  have h7 : Entails.eval a c7032 := h 7031 (by decide)
  have h8 : Entails.eval a c6276 := h 6275 (by decide)
  have h9 : Entails.eval a c7180 := h 7179 (by decide)
  have h10 : Entails.eval a c7393 := h 7392 (by decide)
  have h11 : Entails.eval a c7327 := h 7326 (by decide)
  have h12 : Entails.eval a c7760 := derived7760 a h
  have h13 : Entails.eval a c6948 := h 6947 (by decide)
  have h14 : Entails.eval a c7766 := derived7766 a h
  have h15 : Entails.eval a c5153 := h 5152 (by decide)
  have h16 : Entails.eval a c5223 := h 5222 (by decide)
  have h17 : Entails.eval a c5212 := h 5211 (by decide)
  have h18 : Entails.eval a c5415 := h 5414 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7768 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨60, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7768 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c53, some c5153, some c5223, some c5377, some c68, some c2962, some c3522, some c3539, some c3422, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7768 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7768 : lratChecker f7768 p7768 = .success := by decide +kernel
theorem unsat7768 : Unsatisfiable (PosFin 65) f7768 := by
  apply lratCheckerSound f7768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7768
  · intro a ha; simp [p7768] at ha; subst a; trivial
  · exact checked7768
theorem derived7768 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7768 := by
  apply localUnsat_implies_entails f7768 [c53, c5153, c5223, c5377, c68, c2962, c3522, c3539, c3422] c7768 unsat7768 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c5153 := h 5152 (by decide)
  have h2 : Entails.eval a c5223 := h 5222 (by decide)
  have h3 : Entails.eval a c5377 := h 5376 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c2962 := h 2961 (by decide)
  have h6 : Entails.eval a c3522 := h 3521 (by decide)
  have h7 : Entails.eval a c3539 := h 3538 (by decide)
  have h8 : Entails.eval a c3422 := h 3421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7769 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨20, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨55, by decide⟩, true), (⟨60, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7769 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5239, some c5167, some c5586, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7769 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7769 : lratChecker f7769 p7769 = .success := by decide +kernel
theorem unsat7769 : Unsatisfiable (PosFin 65) f7769 := by
  apply lratCheckerSound f7769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7769
  · intro a ha; simp [p7769] at ha; subst a; trivial
  · exact checked7769
theorem derived7769 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7769 := by
  apply localUnsat_implies_entails f7769 [c5239, c5167, c5586] c7769 unsat7769 (by rfl) a
  have h0 : Entails.eval a c5239 := h 5238 (by decide)
  have h1 : Entails.eval a c5167 := h 5166 (by decide)
  have h2 : Entails.eval a c5586 := h 5585 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7770 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7770 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5371, some c5384, some c5397, some c6209, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p7770 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7770 : lratChecker f7770 p7770 = .success := by decide +kernel
theorem unsat7770 : Unsatisfiable (PosFin 65) f7770 := by
  apply lratCheckerSound f7770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7770
  · intro a ha; simp [p7770] at ha; subst a; trivial
  · exact checked7770
theorem derived7770 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7770 := by
  apply localUnsat_implies_entails f7770 [c5371, c5384, c5397, c6209] c7770 unsat7770 (by rfl) a
  have h0 : Entails.eval a c5371 := h 5370 (by decide)
  have h1 : Entails.eval a c5384 := h 5383 (by decide)
  have h2 : Entails.eval a c5397 := h 5396 (by decide)
  have h3 : Entails.eval a c6209 := h 6208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7771 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨43, by decide⟩, true), (⟨60, by decide⟩, true), (⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7771 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6330, some c7230, some c7458, some c6921, some c7161, some c7184, some c6754, some c7324, some c7768, some c7769, some c5704, some c7770, some c5139, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7771 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7771 : lratChecker f7771 p7771 = .success := by decide +kernel
theorem unsat7771 : Unsatisfiable (PosFin 65) f7771 := by
  apply lratCheckerSound f7771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7771
  · intro a ha; simp [p7771] at ha; subst a; trivial
  · exact checked7771
theorem derived7771 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7771 := by
  apply localUnsat_implies_entails f7771 [c6330, c7230, c7458, c6921, c7161, c7184, c6754, c7324, c7768, c7769, c5704, c7770, c5139] c7771 unsat7771 (by rfl) a
  have h0 : Entails.eval a c6330 := h 6329 (by decide)
  have h1 : Entails.eval a c7230 := h 7229 (by decide)
  have h2 : Entails.eval a c7458 := h 7457 (by decide)
  have h3 : Entails.eval a c6921 := h 6920 (by decide)
  have h4 : Entails.eval a c7161 := h 7160 (by decide)
  have h5 : Entails.eval a c7184 := h 7183 (by decide)
  have h6 : Entails.eval a c6754 := h 6753 (by decide)
  have h7 : Entails.eval a c7324 := h 7323 (by decide)
  have h8 : Entails.eval a c7768 := derived7768 a h
  have h9 : Entails.eval a c7769 := derived7769 a h
  have h10 : Entails.eval a c5704 := h 5703 (by decide)
  have h11 : Entails.eval a c7770 := derived7770 a h
  have h12 : Entails.eval a c5139 := h 5138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7772 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7772 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7649, some c5145, some c5184, some c5354, some c5363, some c5578, some c5690, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7772 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7772 : lratChecker f7772 p7772 = .success := by decide +kernel
theorem unsat7772 : Unsatisfiable (PosFin 65) f7772 := by
  apply lratCheckerSound f7772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7772
  · intro a ha; simp [p7772] at ha; subst a; trivial
  · exact checked7772
theorem derived7772 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7772 := by
  apply localUnsat_implies_entails f7772 [c7649, c5145, c5184, c5354, c5363, c5578, c5690] c7772 unsat7772 (by rfl) a
  have h0 : Entails.eval a c7649 := derived7649 a h
  have h1 : Entails.eval a c5145 := h 5144 (by decide)
  have h2 : Entails.eval a c5184 := h 5183 (by decide)
  have h3 : Entails.eval a c5354 := h 5353 (by decide)
  have h4 : Entails.eval a c5363 := h 5362 (by decide)
  have h5 : Entails.eval a c5578 := h 5577 (by decide)
  have h6 : Entails.eval a c5690 := h 5689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7773 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7773 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7758, some c7712, some c7767, some c7668, some c7771, some c6338, some c6714, some c7468, some c7233, some c7705, some c7637, some c7164, some c6914, some c7343, some c7772, some c54, some c5160, some c5228, some c5442, some c5378, some c6129, some c5622, some c69, some c5487, some c5464, some c5566, some c3512, some c2963, some c3429, some c416, some c465, some c1540, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7773 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked7773 : lratChecker f7773 p7773 = .success := by decide +kernel
theorem unsat7773 : Unsatisfiable (PosFin 65) f7773 := by
  apply lratCheckerSound f7773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7773
  · intro a ha; simp [p7773] at ha; subst a; trivial
  · exact checked7773
theorem derived7773 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7773 := by
  apply localUnsat_implies_entails f7773 [c7758, c7712, c7767, c7668, c7771, c6338, c6714, c7468, c7233, c7705, c7637, c7164, c6914, c7343, c7772, c54, c5160, c5228, c5442, c5378, c6129, c5622, c69, c5487, c5464, c5566, c3512, c2963, c3429, c416, c465, c1540] c7773 unsat7773 (by rfl) a
  have h0 : Entails.eval a c7758 := derived7758 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c7767 := derived7767 a h
  have h3 : Entails.eval a c7668 := derived7668 a h
  have h4 : Entails.eval a c7771 := derived7771 a h
  have h5 : Entails.eval a c6338 := h 6337 (by decide)
  have h6 : Entails.eval a c6714 := h 6713 (by decide)
  have h7 : Entails.eval a c7468 := h 7467 (by decide)
  have h8 : Entails.eval a c7233 := h 7232 (by decide)
  have h9 : Entails.eval a c7705 := derived7705 a h
  have h10 : Entails.eval a c7637 := derived7637 a h
  have h11 : Entails.eval a c7164 := h 7163 (by decide)
  have h12 : Entails.eval a c6914 := h 6913 (by decide)
  have h13 : Entails.eval a c7343 := h 7342 (by decide)
  have h14 : Entails.eval a c7772 := derived7772 a h
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c5160 := h 5159 (by decide)
  have h17 : Entails.eval a c5228 := h 5227 (by decide)
  have h18 : Entails.eval a c5442 := h 5441 (by decide)
  have h19 : Entails.eval a c5378 := h 5377 (by decide)
  have h20 : Entails.eval a c6129 := h 6128 (by decide)
  have h21 : Entails.eval a c5622 := h 5621 (by decide)
  have h22 : Entails.eval a c69 := h 68 (by decide)
  have h23 : Entails.eval a c5487 := h 5486 (by decide)
  have h24 : Entails.eval a c5464 := h 5463 (by decide)
  have h25 : Entails.eval a c5566 := h 5565 (by decide)
  have h26 : Entails.eval a c3512 := h 3511 (by decide)
  have h27 : Entails.eval a c2963 := h 2962 (by decide)
  have h28 : Entails.eval a c3429 := h 3428 (by decide)
  have h29 : Entails.eval a c416 := h 415 (by decide)
  have h30 : Entails.eval a c465 := h 464 (by decide)
  have h31 : Entails.eval a c1540 := h 1539 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7774 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨43, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7774 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6338, some c7468, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7774 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7774 : lratChecker f7774 p7774 = .success := by decide +kernel
theorem unsat7774 : Unsatisfiable (PosFin 65) f7774 := by
  apply lratCheckerSound f7774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7774
  · intro a ha; simp [p7774] at ha; subst a; trivial
  · exact checked7774
theorem derived7774 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7774 := by
  apply localUnsat_implies_entails f7774 [c6338, c7468] c7774 unsat7774 (by rfl) a
  have h0 : Entails.eval a c6338 := h 6337 (by decide)
  have h1 : Entails.eval a c7468 := h 7467 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7775 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7775 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7774, some c6330, some c7458, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7775 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7775 : lratChecker f7775 p7775 = .success := by decide +kernel
theorem unsat7775 : Unsatisfiable (PosFin 65) f7775 := by
  apply lratCheckerSound f7775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7775
  · intro a ha; simp [p7775] at ha; subst a; trivial
  · exact checked7775
theorem derived7775 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7775 := by
  apply localUnsat_implies_entails f7775 [c7774, c6330, c7458] c7775 unsat7775 (by rfl) a
  have h0 : Entails.eval a c7774 := derived7774 a h
  have h1 : Entails.eval a c6330 := h 6329 (by decide)
  have h2 : Entails.eval a c7458 := h 7457 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7776 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7776 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7775, some c6352, some c6345, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7776 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7776 : lratChecker f7776 p7776 = .success := by decide +kernel
theorem unsat7776 : Unsatisfiable (PosFin 65) f7776 := by
  apply lratCheckerSound f7776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7776
  · intro a ha; simp [p7776] at ha; subst a; trivial
  · exact checked7776
theorem derived7776 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7776 := by
  apply localUnsat_implies_entails f7776 [c7775, c6352, c6345] c7776 unsat7776 (by rfl) a
  have h0 : Entails.eval a c7775 := derived7775 a h
  have h1 : Entails.eval a c6352 := h 6351 (by decide)
  have h2 : Entails.eval a c6345 := h 6344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7777 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7777 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7758, some c7712, some c7773, some c7735, some c7776, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7777 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7777 : lratChecker f7777 p7777 = .success := by decide +kernel
theorem unsat7777 : Unsatisfiable (PosFin 65) f7777 := by
  apply lratCheckerSound f7777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7777
  · intro a ha; simp [p7777] at ha; subst a; trivial
  · exact checked7777
theorem derived7777 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7777 := by
  apply localUnsat_implies_entails f7777 [c7758, c7712, c7773, c7735, c7776] c7777 unsat7777 (by rfl) a
  have h0 : Entails.eval a c7758 := derived7758 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c7773 := derived7773 a h
  have h3 : Entails.eval a c7735 := derived7735 a h
  have h4 : Entails.eval a c7776 := derived7776 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7778 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7778 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7047, some c7050, some c7057, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7778 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7778 : lratChecker f7778 p7778 = .success := by decide +kernel
theorem unsat7778 : Unsatisfiable (PosFin 65) f7778 := by
  apply lratCheckerSound f7778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7778
  · intro a ha; simp [p7778] at ha; subst a; trivial
  · exact checked7778
theorem derived7778 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7778 := by
  apply localUnsat_implies_entails f7778 [c7047, c7050, c7057] c7778 unsat7778 (by rfl) a
  have h0 : Entails.eval a c7047 := h 7046 (by decide)
  have h1 : Entails.eval a c7050 := h 7049 (by decide)
  have h2 : Entails.eval a c7057 := h 7056 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7779 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨54, by decide⟩, false), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨40, by decide⟩, false), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7779 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5159, some c5227, some c5208, some c5403, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7779 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7779 : lratChecker f7779 p7779 = .success := by decide +kernel
theorem unsat7779 : Unsatisfiable (PosFin 65) f7779 := by
  apply lratCheckerSound f7779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7779
  · intro a ha; simp [p7779] at ha; subst a; trivial
  · exact checked7779
theorem derived7779 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7779 := by
  apply localUnsat_implies_entails f7779 [c5159, c5227, c5208, c5403] c7779 unsat7779 (by rfl) a
  have h0 : Entails.eval a c5159 := h 5158 (by decide)
  have h1 : Entails.eval a c5227 := h 5226 (by decide)
  have h2 : Entails.eval a c5208 := h 5207 (by decide)
  have h3 : Entails.eval a c5403 := h 5402 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7780 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨54, by decide⟩, false), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7780 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5377, some c5403, some c5251, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7780 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7780 : lratChecker f7780 p7780 = .success := by decide +kernel
theorem unsat7780 : Unsatisfiable (PosFin 65) f7780 := by
  apply lratCheckerSound f7780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7780
  · intro a ha; simp [p7780] at ha; subst a; trivial
  · exact checked7780
theorem derived7780 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7780 := by
  apply localUnsat_implies_entails f7780 [c5377, c5403, c5251] c7780 unsat7780 (by rfl) a
  have h0 : Entails.eval a c5377 := h 5376 (by decide)
  have h1 : Entails.eval a c5403 := h 5402 (by decide)
  have h2 : Entails.eval a c5251 := h 5250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7781 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨40, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7781 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5173, some c5245, some c5589, some c5585, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7781 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7781 : lratChecker f7781 p7781 = .success := by decide +kernel
theorem unsat7781 : Unsatisfiable (PosFin 65) f7781 := by
  apply lratCheckerSound f7781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7781
  · intro a ha; simp [p7781] at ha; subst a; trivial
  · exact checked7781
theorem derived7781 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7781 := by
  apply localUnsat_implies_entails f7781 [c5173, c5245, c5589, c5585] c7781 unsat7781 (by rfl) a
  have h0 : Entails.eval a c5173 := h 5172 (by decide)
  have h1 : Entails.eval a c5245 := h 5244 (by decide)
  have h2 : Entails.eval a c5589 := h 5588 (by decide)
  have h3 : Entails.eval a c5585 := h 5584 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7782 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7782 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7777, some c7758, some c6333, some c6349, some c7461, some c7778, some c7030, some c7239, some c6956, some c7184, some c6319, some c6754, some c7326, some c7413, some c6281, some c7654, some c7779, some c7781, some c7780, some c5131, some c5144, some c5530, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7782 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked7782 : lratChecker f7782 p7782 = .success := by decide +kernel
theorem unsat7782 : Unsatisfiable (PosFin 65) f7782 := by
  apply lratCheckerSound f7782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7782
  · intro a ha; simp [p7782] at ha; subst a; trivial
  · exact checked7782
theorem derived7782 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7782 := by
  apply localUnsat_implies_entails f7782 [c7777, c7758, c6333, c6349, c7461, c7778, c7030, c7239, c6956, c7184, c6319, c6754, c7326, c7413, c6281, c7654, c7779, c7781, c7780, c5131, c5144, c5530] c7782 unsat7782 (by rfl) a
  have h0 : Entails.eval a c7777 := derived7777 a h
  have h1 : Entails.eval a c7758 := derived7758 a h
  have h2 : Entails.eval a c6333 := h 6332 (by decide)
  have h3 : Entails.eval a c6349 := h 6348 (by decide)
  have h4 : Entails.eval a c7461 := h 7460 (by decide)
  have h5 : Entails.eval a c7778 := derived7778 a h
  have h6 : Entails.eval a c7030 := h 7029 (by decide)
  have h7 : Entails.eval a c7239 := h 7238 (by decide)
  have h8 : Entails.eval a c6956 := h 6955 (by decide)
  have h9 : Entails.eval a c7184 := h 7183 (by decide)
  have h10 : Entails.eval a c6319 := h 6318 (by decide)
  have h11 : Entails.eval a c6754 := h 6753 (by decide)
  have h12 : Entails.eval a c7326 := h 7325 (by decide)
  have h13 : Entails.eval a c7413 := h 7412 (by decide)
  have h14 : Entails.eval a c6281 := h 6280 (by decide)
  have h15 : Entails.eval a c7654 := derived7654 a h
  have h16 : Entails.eval a c7779 := derived7779 a h
  have h17 : Entails.eval a c7781 := derived7781 a h
  have h18 : Entails.eval a c7780 := derived7780 a h
  have h19 : Entails.eval a c5131 := h 5130 (by decide)
  have h20 : Entails.eval a c5144 := h 5143 (by decide)
  have h21 : Entails.eval a c5530 := h 5529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7783 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨55, by decide⟩, true), (⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7783 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7758, some c7777, some c6333, some c6349, some c7782, some c6716, some c7461, some c7778, some c7030, some c6951, some c5155, some c5141, some c5127, some c5534, some c5528, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7783 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7783 : lratChecker f7783 p7783 = .success := by decide +kernel
theorem unsat7783 : Unsatisfiable (PosFin 65) f7783 := by
  apply lratCheckerSound f7783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7783
  · intro a ha; simp [p7783] at ha; subst a; trivial
  · exact checked7783
theorem derived7783 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7783 := by
  apply localUnsat_implies_entails f7783 [c7758, c7777, c6333, c6349, c7782, c6716, c7461, c7778, c7030, c6951, c5155, c5141, c5127, c5534, c5528] c7783 unsat7783 (by rfl) a
  have h0 : Entails.eval a c7758 := derived7758 a h
  have h1 : Entails.eval a c7777 := derived7777 a h
  have h2 : Entails.eval a c6333 := h 6332 (by decide)
  have h3 : Entails.eval a c6349 := h 6348 (by decide)
  have h4 : Entails.eval a c7782 := derived7782 a h
  have h5 : Entails.eval a c6716 := h 6715 (by decide)
  have h6 : Entails.eval a c7461 := h 7460 (by decide)
  have h7 : Entails.eval a c7778 := derived7778 a h
  have h8 : Entails.eval a c7030 := h 7029 (by decide)
  have h9 : Entails.eval a c6951 := h 6950 (by decide)
  have h10 : Entails.eval a c5155 := h 5154 (by decide)
  have h11 : Entails.eval a c5141 := h 5140 (by decide)
  have h12 : Entails.eval a c5127 := h 5126 (by decide)
  have h13 : Entails.eval a c5534 := h 5533 (by decide)
  have h14 : Entails.eval a c5528 := h 5527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7784 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7784 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5581, some c5597, some c5180, some c6052, some c5733, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7784 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7784 : lratChecker f7784 p7784 = .success := by decide +kernel
theorem unsat7784 : Unsatisfiable (PosFin 65) f7784 := by
  apply lratCheckerSound f7784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7784
  · intro a ha; simp [p7784] at ha; subst a; trivial
  · exact checked7784
theorem derived7784 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7784 := by
  apply localUnsat_implies_entails f7784 [c5581, c5597, c5180, c6052, c5733] c7784 unsat7784 (by rfl) a
  have h0 : Entails.eval a c5581 := h 5580 (by decide)
  have h1 : Entails.eval a c5597 := h 5596 (by decide)
  have h2 : Entails.eval a c5180 := h 5179 (by decide)
  have h3 : Entails.eval a c6052 := h 6051 (by decide)
  have h4 : Entails.eval a c5733 := h 5732 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7785 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨17, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7785 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5172, some c5165, some c5373, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7785 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7785 : lratChecker f7785 p7785 = .success := by decide +kernel
theorem unsat7785 : Unsatisfiable (PosFin 65) f7785 := by
  apply lratCheckerSound f7785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7785
  · intro a ha; simp [p7785] at ha; subst a; trivial
  · exact checked7785
theorem derived7785 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7785 := by
  apply localUnsat_implies_entails f7785 [c5172, c5165, c5373] c7785 unsat7785 (by rfl) a
  have h0 : Entails.eval a c5172 := h 5171 (by decide)
  have h1 : Entails.eval a c5165 := h 5164 (by decide)
  have h2 : Entails.eval a c5373 := h 5372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7786 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7786 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7777, some c7758, some c6333, some c6349, some c7461, some c7778, some c7030, some c7782, some c6951, some c7232, some c6716, some c6319, some c7413, some c7310, some c7783, some c7785, some c7784, some c5210, some c5225, some c5412, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7786 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7786 : lratChecker f7786 p7786 = .success := by decide +kernel
theorem unsat7786 : Unsatisfiable (PosFin 65) f7786 := by
  apply lratCheckerSound f7786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7786
  · intro a ha; simp [p7786] at ha; subst a; trivial
  · exact checked7786
theorem derived7786 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7786 := by
  apply localUnsat_implies_entails f7786 [c7777, c7758, c6333, c6349, c7461, c7778, c7030, c7782, c6951, c7232, c6716, c6319, c7413, c7310, c7783, c7785, c7784, c5210, c5225, c5412] c7786 unsat7786 (by rfl) a
  have h0 : Entails.eval a c7777 := derived7777 a h
  have h1 : Entails.eval a c7758 := derived7758 a h
  have h2 : Entails.eval a c6333 := h 6332 (by decide)
  have h3 : Entails.eval a c6349 := h 6348 (by decide)
  have h4 : Entails.eval a c7461 := h 7460 (by decide)
  have h5 : Entails.eval a c7778 := derived7778 a h
  have h6 : Entails.eval a c7030 := h 7029 (by decide)
  have h7 : Entails.eval a c7782 := derived7782 a h
  have h8 : Entails.eval a c6951 := h 6950 (by decide)
  have h9 : Entails.eval a c7232 := h 7231 (by decide)
  have h10 : Entails.eval a c6716 := h 6715 (by decide)
  have h11 : Entails.eval a c6319 := h 6318 (by decide)
  have h12 : Entails.eval a c7413 := h 7412 (by decide)
  have h13 : Entails.eval a c7310 := h 7309 (by decide)
  have h14 : Entails.eval a c7783 := derived7783 a h
  have h15 : Entails.eval a c7785 := derived7785 a h
  have h16 : Entails.eval a c7784 := derived7784 a h
  have h17 : Entails.eval a c5210 := h 5209 (by decide)
  have h18 : Entails.eval a c5225 := h 5224 (by decide)
  have h19 : Entails.eval a c5412 := h 5411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7787 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7787 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7758, some c7777, some c6349, some c6333, some c7461, some c7030, some c7778, some c7786, some c6714, some c7233, some c7185, some c7637, some c6274, some c7333, some c7413, some c6908, some c7772, some c5160, some c5228, some c5211, some c5414, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7787 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked7787 : lratChecker f7787 p7787 = .success := by decide +kernel
theorem unsat7787 : Unsatisfiable (PosFin 65) f7787 := by
  apply lratCheckerSound f7787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7787
  · intro a ha; simp [p7787] at ha; subst a; trivial
  · exact checked7787
theorem derived7787 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7787 := by
  apply localUnsat_implies_entails f7787 [c7758, c7777, c6349, c6333, c7461, c7030, c7778, c7786, c6714, c7233, c7185, c7637, c6274, c7333, c7413, c6908, c7772, c5160, c5228, c5211, c5414] c7787 unsat7787 (by rfl) a
  have h0 : Entails.eval a c7758 := derived7758 a h
  have h1 : Entails.eval a c7777 := derived7777 a h
  have h2 : Entails.eval a c6349 := h 6348 (by decide)
  have h3 : Entails.eval a c6333 := h 6332 (by decide)
  have h4 : Entails.eval a c7461 := h 7460 (by decide)
  have h5 : Entails.eval a c7030 := h 7029 (by decide)
  have h6 : Entails.eval a c7778 := derived7778 a h
  have h7 : Entails.eval a c7786 := derived7786 a h
  have h8 : Entails.eval a c6714 := h 6713 (by decide)
  have h9 : Entails.eval a c7233 := h 7232 (by decide)
  have h10 : Entails.eval a c7185 := h 7184 (by decide)
  have h11 : Entails.eval a c7637 := derived7637 a h
  have h12 : Entails.eval a c6274 := h 6273 (by decide)
  have h13 : Entails.eval a c7333 := h 7332 (by decide)
  have h14 : Entails.eval a c7413 := h 7412 (by decide)
  have h15 : Entails.eval a c6908 := h 6907 (by decide)
  have h16 : Entails.eval a c7772 := derived7772 a h
  have h17 : Entails.eval a c5160 := h 5159 (by decide)
  have h18 : Entails.eval a c5228 := h 5227 (by decide)
  have h19 : Entails.eval a c5211 := h 5210 (by decide)
  have h20 : Entails.eval a c5414 := h 5413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7788 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7788 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6349, some c6333, some c7461, some c6724, some c7637, some c7413, some c5160, some c5228, some c5211, some c5414, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7788 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7788 : lratChecker f7788 p7788 = .success := by decide +kernel
theorem unsat7788 : Unsatisfiable (PosFin 65) f7788 := by
  apply lratCheckerSound f7788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7788
  · intro a ha; simp [p7788] at ha; subst a; trivial
  · exact checked7788
theorem derived7788 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7788 := by
  apply localUnsat_implies_entails f7788 [c6349, c6333, c7461, c6724, c7637, c7413, c5160, c5228, c5211, c5414] c7788 unsat7788 (by rfl) a
  have h0 : Entails.eval a c6349 := h 6348 (by decide)
  have h1 : Entails.eval a c6333 := h 6332 (by decide)
  have h2 : Entails.eval a c7461 := h 7460 (by decide)
  have h3 : Entails.eval a c6724 := h 6723 (by decide)
  have h4 : Entails.eval a c7637 := derived7637 a h
  have h5 : Entails.eval a c7413 := h 7412 (by decide)
  have h6 : Entails.eval a c5160 := h 5159 (by decide)
  have h7 : Entails.eval a c5228 := h 5227 (by decide)
  have h8 : Entails.eval a c5211 := h 5210 (by decide)
  have h9 : Entails.eval a c5414 := h 5413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7789 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7789 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6333, some c6349, some c7461, some c7030, some c6724, some c7637, some c6282, some c7413, some c7310, some c6908, some c6664, some c7223, some c7788, some c7649, some c5145, some c5184, some c5190, some c5329, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7789 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7789 : lratChecker f7789 p7789 = .success := by decide +kernel
theorem unsat7789 : Unsatisfiable (PosFin 65) f7789 := by
  apply lratCheckerSound f7789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7789
  · intro a ha; simp [p7789] at ha; subst a; trivial
  · exact checked7789
theorem derived7789 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7789 := by
  apply localUnsat_implies_entails f7789 [c6333, c6349, c7461, c7030, c6724, c7637, c6282, c7413, c7310, c6908, c6664, c7223, c7788, c7649, c5145, c5184, c5190, c5329] c7789 unsat7789 (by rfl) a
  have h0 : Entails.eval a c6333 := h 6332 (by decide)
  have h1 : Entails.eval a c6349 := h 6348 (by decide)
  have h2 : Entails.eval a c7461 := h 7460 (by decide)
  have h3 : Entails.eval a c7030 := h 7029 (by decide)
  have h4 : Entails.eval a c6724 := h 6723 (by decide)
  have h5 : Entails.eval a c7637 := derived7637 a h
  have h6 : Entails.eval a c6282 := h 6281 (by decide)
  have h7 : Entails.eval a c7413 := h 7412 (by decide)
  have h8 : Entails.eval a c7310 := h 7309 (by decide)
  have h9 : Entails.eval a c6908 := h 6907 (by decide)
  have h10 : Entails.eval a c6664 := h 6663 (by decide)
  have h11 : Entails.eval a c7223 := h 7222 (by decide)
  have h12 : Entails.eval a c7788 := derived7788 a h
  have h13 : Entails.eval a c7649 := derived7649 a h
  have h14 : Entails.eval a c5145 := h 5144 (by decide)
  have h15 : Entails.eval a c5184 := h 5183 (by decide)
  have h16 : Entails.eval a c5190 := h 5189 (by decide)
  have h17 : Entails.eval a c5329 := h 5328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7790 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨64, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7790 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5329, some c5432, some c5414, some c6041, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7790 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7790 : lratChecker f7790 p7790 = .success := by decide +kernel
theorem unsat7790 : Unsatisfiable (PosFin 65) f7790 := by
  apply lratCheckerSound f7790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7790
  · intro a ha; simp [p7790] at ha; subst a; trivial
  · exact checked7790
theorem derived7790 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7790 := by
  apply localUnsat_implies_entails f7790 [c5329, c5432, c5414, c6041] c7790 unsat7790 (by rfl) a
  have h0 : Entails.eval a c5329 := h 5328 (by decide)
  have h1 : Entails.eval a c5432 := h 5431 (by decide)
  have h2 : Entails.eval a c5414 := h 5413 (by decide)
  have h3 : Entails.eval a c6041 := h 6040 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7791 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7791 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7310, some c7326, some c7496, some c7492, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7791 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7791 : lratChecker f7791 p7791 = .success := by decide +kernel
theorem unsat7791 : Unsatisfiable (PosFin 65) f7791 := by
  apply lratCheckerSound f7791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7791
  · intro a ha; simp [p7791] at ha; subst a; trivial
  · exact checked7791
theorem derived7791 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7791 := by
  apply localUnsat_implies_entails f7791 [c7310, c7326, c7496, c7492] c7791 unsat7791 (by rfl) a
  have h0 : Entails.eval a c7310 := h 7309 (by decide)
  have h1 : Entails.eval a c7326 := h 7325 (by decide)
  have h2 : Entails.eval a c7496 := h 7495 (by decide)
  have h3 : Entails.eval a c7492 := h 7491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7792 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7792 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7790, some c5385, some c5707, some c5765, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7792 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7792 : lratChecker f7792 p7792 = .success := by decide +kernel
theorem unsat7792 : Unsatisfiable (PosFin 65) f7792 := by
  apply lratCheckerSound f7792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7792
  · intro a ha; simp [p7792] at ha; subst a; trivial
  · exact checked7792
theorem derived7792 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7792 := by
  apply localUnsat_implies_entails f7792 [c7790, c5385, c5707, c5765] c7792 unsat7792 (by rfl) a
  have h0 : Entails.eval a c7790 := derived7790 a h
  have h1 : Entails.eval a c5385 := h 5384 (by decide)
  have h2 : Entails.eval a c5707 := h 5706 (by decide)
  have h3 : Entails.eval a c5765 := h 5764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7793 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨45, by decide⟩, true), (⟨42, by decide⟩, true), (⟨43, by decide⟩, true), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7793 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7461, some c7637, some c7494, some c6753, some c6727, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7793 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7793 : lratChecker f7793 p7793 = .success := by decide +kernel
theorem unsat7793 : Unsatisfiable (PosFin 65) f7793 := by
  apply lratCheckerSound f7793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7793
  · intro a ha; simp [p7793] at ha; subst a; trivial
  · exact checked7793
theorem derived7793 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7793 := by
  apply localUnsat_implies_entails f7793 [c7461, c7637, c7494, c6753, c6727] c7793 unsat7793 (by rfl) a
  have h0 : Entails.eval a c7461 := h 7460 (by decide)
  have h1 : Entails.eval a c7637 := derived7637 a h
  have h2 : Entails.eval a c7494 := h 7493 (by decide)
  have h3 : Entails.eval a c6753 := h 6752 (by decide)
  have h4 : Entails.eval a c6727 := h 6726 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7794 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, true), (⟨45, by decide⟩, true), (⟨42, by decide⟩, true), (⟨43, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7794 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6753, some c6727, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7794 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7794 : lratChecker f7794 p7794 = .success := by decide +kernel
theorem unsat7794 : Unsatisfiable (PosFin 65) f7794 := by
  apply lratCheckerSound f7794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7794
  · intro a ha; simp [p7794] at ha; subst a; trivial
  · exact checked7794
theorem derived7794 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7794 := by
  apply localUnsat_implies_entails f7794 [c6753, c6727] c7794 unsat7794 (by rfl) a
  have h0 : Entails.eval a c6753 := h 6752 (by decide)
  have h1 : Entails.eval a c6727 := h 6726 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7795 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨20, by decide⟩, true), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7795 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7790, some c7792, some c5251, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7795 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7795 : lratChecker f7795 p7795 = .success := by decide +kernel
theorem unsat7795 : Unsatisfiable (PosFin 65) f7795 := by
  apply lratCheckerSound f7795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7795
  · intro a ha; simp [p7795] at ha; subst a; trivial
  · exact checked7795
theorem derived7795 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7795 := by
  apply localUnsat_implies_entails f7795 [c7790, c7792, c5251] c7795 unsat7795 (by rfl) a
  have h0 : Entails.eval a c7790 := derived7790 a h
  have h1 : Entails.eval a c7792 := derived7792 a h
  have h2 : Entails.eval a c5251 := h 5250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7796 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨50, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7796 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1505, some c1943, some c2007, some c4036, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7796 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7796 : lratChecker f7796 p7796 = .success := by decide +kernel
theorem unsat7796 : Unsatisfiable (PosFin 65) f7796 := by
  apply lratCheckerSound f7796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7796
  · intro a ha; simp [p7796] at ha; subst a; trivial
  · exact checked7796
theorem derived7796 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7796 := by
  apply localUnsat_implies_entails f7796 [c1505, c1943, c2007, c4036] c7796 unsat7796 (by rfl) a
  have h0 : Entails.eval a c1505 := h 1504 (by decide)
  have h1 : Entails.eval a c1943 := h 1942 (by decide)
  have h2 : Entails.eval a c2007 := h 2006 (by decide)
  have h3 : Entails.eval a c4036 := h 4035 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7797 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨50, by decide⟩, false), (⟨36, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7797 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c494, some c534, some c2953, some c3158, some c3541, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7797 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7797 : lratChecker f7797 p7797 = .success := by decide +kernel
theorem unsat7797 : Unsatisfiable (PosFin 65) f7797 := by
  apply lratCheckerSound f7797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7797
  · intro a ha; simp [p7797] at ha; subst a; trivial
  · exact checked7797
theorem derived7797 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7797 := by
  apply localUnsat_implies_entails f7797 [c494, c534, c2953, c3158, c3541] c7797 unsat7797 (by rfl) a
  have h0 : Entails.eval a c494 := h 493 (by decide)
  have h1 : Entails.eval a c534 := h 533 (by decide)
  have h2 : Entails.eval a c2953 := h 2952 (by decide)
  have h3 : Entails.eval a c3158 := h 3157 (by decide)
  have h4 : Entails.eval a c3541 := h 3540 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7798 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7798 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7787, some c7758, some c7712, some c6349, some c6333, some c7461, some c7030, some c7789, some c7791, some c7793, some c7413, some c7797, some c7796, some c6, some c7790, some c7795, some c5211, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7798 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7798 : lratChecker f7798 p7798 = .success := by decide +kernel
theorem unsat7798 : Unsatisfiable (PosFin 65) f7798 := by
  apply lratCheckerSound f7798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7798
  · intro a ha; simp [p7798] at ha; subst a; trivial
  · exact checked7798
theorem derived7798 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7798 := by
  apply localUnsat_implies_entails f7798 [c7787, c7758, c7712, c6349, c6333, c7461, c7030, c7789, c7791, c7793, c7413, c7797, c7796, c6, c7790, c7795, c5211] c7798 unsat7798 (by rfl) a
  have h0 : Entails.eval a c7787 := derived7787 a h
  have h1 : Entails.eval a c7758 := derived7758 a h
  have h2 : Entails.eval a c7712 := derived7712 a h
  have h3 : Entails.eval a c6349 := h 6348 (by decide)
  have h4 : Entails.eval a c6333 := h 6332 (by decide)
  have h5 : Entails.eval a c7461 := h 7460 (by decide)
  have h6 : Entails.eval a c7030 := h 7029 (by decide)
  have h7 : Entails.eval a c7789 := derived7789 a h
  have h8 : Entails.eval a c7791 := derived7791 a h
  have h9 : Entails.eval a c7793 := derived7793 a h
  have h10 : Entails.eval a c7413 := h 7412 (by decide)
  have h11 : Entails.eval a c7797 := derived7797 a h
  have h12 : Entails.eval a c7796 := derived7796 a h
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c7790 := derived7790 a h
  have h15 : Entails.eval a c7795 := derived7795 a h
  have h16 : Entails.eval a c5211 := h 5210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7799 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨39, by decide⟩, false), (⟨1, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7799 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c429, some c3, some c6328, some c7776, some c7041, some c7228, some c6344, some c7174, some c7322, some c7118, some c5249, some c7770, some c5382, some c6724, some c7034, some c6914, some c425, some c414, some c2386, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7799 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7799 : lratChecker f7799 p7799 = .success := by decide +kernel
theorem unsat7799 : Unsatisfiable (PosFin 65) f7799 := by
  apply lratCheckerSound f7799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7799
  · intro a ha; simp [p7799] at ha; subst a; trivial
  · exact checked7799
theorem derived7799 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7799 := by
  apply localUnsat_implies_entails f7799 [c429, c3, c6328, c7776, c7041, c7228, c6344, c7174, c7322, c7118, c5249, c7770, c5382, c6724, c7034, c6914, c425, c414, c2386] c7799 unsat7799 (by rfl) a
  have h0 : Entails.eval a c429 := h 428 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c6328 := h 6327 (by decide)
  have h3 : Entails.eval a c7776 := derived7776 a h
  have h4 : Entails.eval a c7041 := h 7040 (by decide)
  have h5 : Entails.eval a c7228 := h 7227 (by decide)
  have h6 : Entails.eval a c6344 := h 6343 (by decide)
  have h7 : Entails.eval a c7174 := h 7173 (by decide)
  have h8 : Entails.eval a c7322 := h 7321 (by decide)
  have h9 : Entails.eval a c7118 := h 7117 (by decide)
  have h10 : Entails.eval a c5249 := h 5248 (by decide)
  have h11 : Entails.eval a c7770 := derived7770 a h
  have h12 : Entails.eval a c5382 := h 5381 (by decide)
  have h13 : Entails.eval a c6724 := h 6723 (by decide)
  have h14 : Entails.eval a c7034 := h 7033 (by decide)
  have h15 : Entails.eval a c6914 := h 6913 (by decide)
  have h16 : Entails.eval a c425 := h 424 (by decide)
  have h17 : Entails.eval a c414 := h 413 (by decide)
  have h18 : Entails.eval a c2386 := h 2385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7800 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7800 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5325, some c5407, some c5241, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7800 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7800 : lratChecker f7800 p7800 = .success := by decide +kernel
theorem unsat7800 : Unsatisfiable (PosFin 65) f7800 := by
  apply lratCheckerSound f7800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7800
  · intro a ha; simp [p7800] at ha; subst a; trivial
  · exact checked7800
theorem derived7800 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7800 := by
  apply localUnsat_implies_entails f7800 [c5325, c5407, c5241] c7800 unsat7800 (by rfl) a
  have h0 : Entails.eval a c5325 := h 5324 (by decide)
  have h1 : Entails.eval a c5407 := h 5406 (by decide)
  have h2 : Entails.eval a c5241 := h 5240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7801 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7801 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6724, some c6728, some c6723, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7801 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7801 : lratChecker f7801 p7801 = .success := by decide +kernel
theorem unsat7801 : Unsatisfiable (PosFin 65) f7801 := by
  apply lratCheckerSound f7801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7801
  · intro a ha; simp [p7801] at ha; subst a; trivial
  · exact checked7801
theorem derived7801 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7801 := by
  apply localUnsat_implies_entails f7801 [c6724, c6728, c6723] c7801 unsat7801 (by rfl) a
  have h0 : Entails.eval a c6724 := h 6723 (by decide)
  have h1 : Entails.eval a c6728 := h 6727 (by decide)
  have h2 : Entails.eval a c6723 := h 6722 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7802 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7802 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6344, some c7776, some c6328, some c7801, some c7637, some c7408, some c7041, some c7228, some c3, some c7799, some c7800, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7802 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7802 : lratChecker f7802 p7802 = .success := by decide +kernel
theorem unsat7802 : Unsatisfiable (PosFin 65) f7802 := by
  apply lratCheckerSound f7802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7802
  · intro a ha; simp [p7802] at ha; subst a; trivial
  · exact checked7802
theorem derived7802 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7802 := by
  apply localUnsat_implies_entails f7802 [c6344, c7776, c6328, c7801, c7637, c7408, c7041, c7228, c3, c7799, c7800] c7802 unsat7802 (by rfl) a
  have h0 : Entails.eval a c6344 := h 6343 (by decide)
  have h1 : Entails.eval a c7776 := derived7776 a h
  have h2 : Entails.eval a c6328 := h 6327 (by decide)
  have h3 : Entails.eval a c7801 := derived7801 a h
  have h4 : Entails.eval a c7637 := derived7637 a h
  have h5 : Entails.eval a c7408 := h 7407 (by decide)
  have h6 : Entails.eval a c7041 := h 7040 (by decide)
  have h7 : Entails.eval a c7228 := h 7227 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c7799 := derived7799 a h
  have h10 : Entails.eval a c7800 := derived7800 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7803 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨55, by decide⟩, true), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7803 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7800, some c7770, some c5249, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7803 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7803 : lratChecker f7803 p7803 = .success := by decide +kernel
theorem unsat7803 : Unsatisfiable (PosFin 65) f7803 := by
  apply lratCheckerSound f7803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7803
  · intro a ha; simp [p7803] at ha; subst a; trivial
  · exact checked7803
theorem derived7803 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7803 := by
  apply localUnsat_implies_entails f7803 [c7800, c7770, c5249] c7803 unsat7803 (by rfl) a
  have h0 : Entails.eval a c7800 := derived7800 a h
  have h1 : Entails.eval a c7770 := derived7770 a h
  have h2 : Entails.eval a c5249 := h 5248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7804 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨55, by decide⟩, true), (⟨34, by decide⟩, false), (⟨51, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7804 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5156, some c5130, some c5529, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7804 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7804 : lratChecker f7804 p7804 = .success := by decide +kernel
theorem unsat7804 : Unsatisfiable (PosFin 65) f7804 := by
  apply lratCheckerSound f7804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7804
  · intro a ha; simp [p7804] at ha; subst a; trivial
  · exact checked7804
theorem derived7804 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7804 := by
  apply localUnsat_implies_entails f7804 [c5156, c5130, c5529] c7804 unsat7804 (by rfl) a
  have h0 : Entails.eval a c5156 := h 5155 (by decide)
  have h1 : Entails.eval a c5130 := h 5129 (by decide)
  have h2 : Entails.eval a c5529 := h 5528 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7805 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7805 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6344, some c7776, some c6328, some c7801, some c7637, some c7408, some c7041, some c7228, some c7174, some c7322, some c6921, some c7803, some c5139, some c7804, some c5151, some c5134, some c5535, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7805 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7805 : lratChecker f7805 p7805 = .success := by decide +kernel
theorem unsat7805 : Unsatisfiable (PosFin 65) f7805 := by
  apply lratCheckerSound f7805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7805
  · intro a ha; simp [p7805] at ha; subst a; trivial
  · exact checked7805
theorem derived7805 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7805 := by
  apply localUnsat_implies_entails f7805 [c6344, c7776, c6328, c7801, c7637, c7408, c7041, c7228, c7174, c7322, c6921, c7803, c5139, c7804, c5151, c5134, c5535] c7805 unsat7805 (by rfl) a
  have h0 : Entails.eval a c6344 := h 6343 (by decide)
  have h1 : Entails.eval a c7776 := derived7776 a h
  have h2 : Entails.eval a c6328 := h 6327 (by decide)
  have h3 : Entails.eval a c7801 := derived7801 a h
  have h4 : Entails.eval a c7637 := derived7637 a h
  have h5 : Entails.eval a c7408 := h 7407 (by decide)
  have h6 : Entails.eval a c7041 := h 7040 (by decide)
  have h7 : Entails.eval a c7228 := h 7227 (by decide)
  have h8 : Entails.eval a c7174 := h 7173 (by decide)
  have h9 : Entails.eval a c7322 := h 7321 (by decide)
  have h10 : Entails.eval a c6921 := h 6920 (by decide)
  have h11 : Entails.eval a c7803 := derived7803 a h
  have h12 : Entails.eval a c5139 := h 5138 (by decide)
  have h13 : Entails.eval a c7804 := derived7804 a h
  have h14 : Entails.eval a c5151 := h 5150 (by decide)
  have h15 : Entails.eval a c5134 := h 5133 (by decide)
  have h16 : Entails.eval a c5535 := h 5534 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7806 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7806 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6328, some c7776, some c7041, some c7228, some c6344, some c7174, some c7322, some c7118, some c7034, some c6914, some c7801, some c5151, some c5145, some c7649, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7806 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7806 : lratChecker f7806 p7806 = .success := by decide +kernel
theorem unsat7806 : Unsatisfiable (PosFin 65) f7806 := by
  apply lratCheckerSound f7806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7806
  · intro a ha; simp [p7806] at ha; subst a; trivial
  · exact checked7806
theorem derived7806 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7806 := by
  apply localUnsat_implies_entails f7806 [c6328, c7776, c7041, c7228, c6344, c7174, c7322, c7118, c7034, c6914, c7801, c5151, c5145, c7649] c7806 unsat7806 (by rfl) a
  have h0 : Entails.eval a c6328 := h 6327 (by decide)
  have h1 : Entails.eval a c7776 := derived7776 a h
  have h2 : Entails.eval a c7041 := h 7040 (by decide)
  have h3 : Entails.eval a c7228 := h 7227 (by decide)
  have h4 : Entails.eval a c6344 := h 6343 (by decide)
  have h5 : Entails.eval a c7174 := h 7173 (by decide)
  have h6 : Entails.eval a c7322 := h 7321 (by decide)
  have h7 : Entails.eval a c7118 := h 7117 (by decide)
  have h8 : Entails.eval a c7034 := h 7033 (by decide)
  have h9 : Entails.eval a c6914 := h 6913 (by decide)
  have h10 : Entails.eval a c7801 := derived7801 a h
  have h11 : Entails.eval a c5151 := h 5150 (by decide)
  have h12 : Entails.eval a c5145 := h 5144 (by decide)
  have h13 : Entails.eval a c7649 := derived7649 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7807 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7807 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7758, some c7787, some c7798, some c6328, some c6344, some c7776, some c7041, some c7228, some c7801, some c7637, some c7408, some c7802, some c7805, some c7806, some c7800, some c73, some c1497, some c1935, some c520, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7807 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7807 : lratChecker f7807 p7807 = .success := by decide +kernel
theorem unsat7807 : Unsatisfiable (PosFin 65) f7807 := by
  apply lratCheckerSound f7807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7807
  · intro a ha; simp [p7807] at ha; subst a; trivial
  · exact checked7807
theorem derived7807 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7807 := by
  apply localUnsat_implies_entails f7807 [c7712, c7758, c7787, c7798, c6328, c6344, c7776, c7041, c7228, c7801, c7637, c7408, c7802, c7805, c7806, c7800, c73, c1497, c1935, c520] c7807 unsat7807 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7758 := derived7758 a h
  have h2 : Entails.eval a c7787 := derived7787 a h
  have h3 : Entails.eval a c7798 := derived7798 a h
  have h4 : Entails.eval a c6328 := h 6327 (by decide)
  have h5 : Entails.eval a c6344 := h 6343 (by decide)
  have h6 : Entails.eval a c7776 := derived7776 a h
  have h7 : Entails.eval a c7041 := h 7040 (by decide)
  have h8 : Entails.eval a c7228 := h 7227 (by decide)
  have h9 : Entails.eval a c7801 := derived7801 a h
  have h10 : Entails.eval a c7637 := derived7637 a h
  have h11 : Entails.eval a c7408 := h 7407 (by decide)
  have h12 : Entails.eval a c7802 := derived7802 a h
  have h13 : Entails.eval a c7805 := derived7805 a h
  have h14 : Entails.eval a c7806 := derived7806 a h
  have h15 : Entails.eval a c7800 := derived7800 a h
  have h16 : Entails.eval a c73 := h 72 (by decide)
  have h17 : Entails.eval a c1497 := h 1496 (by decide)
  have h18 : Entails.eval a c1935 := h 1934 (by decide)
  have h19 : Entails.eval a c520 := h 519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7808 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨55, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7808 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7807, some c6293, some c6282, some c7606, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7808 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7808 : lratChecker f7808 p7808 = .success := by decide +kernel
theorem unsat7808 : Unsatisfiable (PosFin 65) f7808 := by
  apply lratCheckerSound f7808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7808
  · intro a ha; simp [p7808] at ha; subst a; trivial
  · exact checked7808
theorem derived7808 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7808 := by
  apply localUnsat_implies_entails f7808 [c7807, c6293, c6282, c7606] c7808 unsat7808 (by rfl) a
  have h0 : Entails.eval a c7807 := derived7807 a h
  have h1 : Entails.eval a c6293 := h 6292 (by decide)
  have h2 : Entails.eval a c6282 := h 6281 (by decide)
  have h3 : Entails.eval a c7606 := derived7606 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7809 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7809 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7807, some c7808, some c6611, some c6620, some c6568, some c6822, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7809 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7809 : lratChecker f7809 p7809 = .success := by decide +kernel
theorem unsat7809 : Unsatisfiable (PosFin 65) f7809 := by
  apply lratCheckerSound f7809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7809
  · intro a ha; simp [p7809] at ha; subst a; trivial
  · exact checked7809
theorem derived7809 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7809 := by
  apply localUnsat_implies_entails f7809 [c7807, c7808, c6611, c6620, c6568, c6822] c7809 unsat7809 (by rfl) a
  have h0 : Entails.eval a c7807 := derived7807 a h
  have h1 : Entails.eval a c7808 := derived7808 a h
  have h2 : Entails.eval a c6611 := h 6610 (by decide)
  have h3 : Entails.eval a c6620 := h 6619 (by decide)
  have h4 : Entails.eval a c6568 := h 6567 (by decide)
  have h5 : Entails.eval a c6822 := h 6821 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7810 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7810 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7809, some c7807, some c7712, some c6301, some c6317, some c7801, some c7606, some c6487, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7810 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7810 : lratChecker f7810 p7810 = .success := by decide +kernel
theorem unsat7810 : Unsatisfiable (PosFin 65) f7810 := by
  apply lratCheckerSound f7810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7810
  · intro a ha; simp [p7810] at ha; subst a; trivial
  · exact checked7810
theorem derived7810 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7810 := by
  apply localUnsat_implies_entails f7810 [c7809, c7807, c7712, c6301, c6317, c7801, c7606, c6487] c7810 unsat7810 (by rfl) a
  have h0 : Entails.eval a c7809 := derived7809 a h
  have h1 : Entails.eval a c7807 := derived7807 a h
  have h2 : Entails.eval a c7712 := derived7712 a h
  have h3 : Entails.eval a c6301 := h 6300 (by decide)
  have h4 : Entails.eval a c6317 := h 6316 (by decide)
  have h5 : Entails.eval a c7801 := derived7801 a h
  have h6 : Entails.eval a c7606 := derived7606 a h
  have h7 : Entails.eval a c6487 := h 6486 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7811 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7811 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7809, some c7807, some c7712, some c7810, some c6567, some c6572, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7811 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7811 : lratChecker f7811 p7811 = .success := by decide +kernel
theorem unsat7811 : Unsatisfiable (PosFin 65) f7811 := by
  apply lratCheckerSound f7811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7811
  · intro a ha; simp [p7811] at ha; subst a; trivial
  · exact checked7811
theorem derived7811 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7811 := by
  apply localUnsat_implies_entails f7811 [c7809, c7807, c7712, c7810, c6567, c6572] c7811 unsat7811 (by rfl) a
  have h0 : Entails.eval a c7809 := derived7809 a h
  have h1 : Entails.eval a c7807 := derived7807 a h
  have h2 : Entails.eval a c7712 := derived7712 a h
  have h3 : Entails.eval a c7810 := derived7810 a h
  have h4 : Entails.eval a c6567 := h 6566 (by decide)
  have h5 : Entails.eval a c6572 := h 6571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7812 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7812 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6284, some c6280, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7812 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7812 : lratChecker f7812 p7812 = .success := by decide +kernel
theorem unsat7812 : Unsatisfiable (PosFin 65) f7812 := by
  apply lratCheckerSound f7812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7812
  · intro a ha; simp [p7812] at ha; subst a; trivial
  · exact checked7812
theorem derived7812 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7812 := by
  apply localUnsat_implies_entails f7812 [c6284, c6280] c7812 unsat7812 (by rfl) a
  have h0 : Entails.eval a c6284 := h 6283 (by decide)
  have h1 : Entails.eval a c6280 := h 6279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7813 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7813 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7807, some c7712, some c7809, some c7811, some c7812, some c7074, some c7064, some c6739, some c6745, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7813 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7813 : lratChecker f7813 p7813 = .success := by decide +kernel
theorem unsat7813 : Unsatisfiable (PosFin 65) f7813 := by
  apply lratCheckerSound f7813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7813
  · intro a ha; simp [p7813] at ha; subst a; trivial
  · exact checked7813
theorem derived7813 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7813 := by
  apply localUnsat_implies_entails f7813 [c7807, c7712, c7809, c7811, c7812, c7074, c7064, c6739, c6745] c7813 unsat7813 (by rfl) a
  have h0 : Entails.eval a c7807 := derived7807 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c7809 := derived7809 a h
  have h3 : Entails.eval a c7811 := derived7811 a h
  have h4 : Entails.eval a c7812 := derived7812 a h
  have h5 : Entails.eval a c7074 := h 7073 (by decide)
  have h6 : Entails.eval a c7064 := h 7063 (by decide)
  have h7 : Entails.eval a c6739 := h 6738 (by decide)
  have h8 : Entails.eval a c6745 := h 6744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7814 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨55, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7814 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7725, some c7522, some c7196, some c6386, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7814 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7814 : lratChecker f7814 p7814 = .success := by decide +kernel
theorem unsat7814 : Unsatisfiable (PosFin 65) f7814 := by
  apply lratCheckerSound f7814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7814
  · intro a ha; simp [p7814] at ha; subst a; trivial
  · exact checked7814
theorem derived7814 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7814 := by
  apply localUnsat_implies_entails f7814 [c7725, c7522, c7196, c6386] c7814 unsat7814 (by rfl) a
  have h0 : Entails.eval a c7725 := derived7725 a h
  have h1 : Entails.eval a c7522 := h 7521 (by decide)
  have h2 : Entails.eval a c7196 := h 7195 (by decide)
  have h3 : Entails.eval a c6386 := h 6385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7815 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7815 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7814, some c7074, some c6782, some c7064, some c6941, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7815 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7815 : lratChecker f7815 p7815 = .success := by decide +kernel
theorem unsat7815 : Unsatisfiable (PosFin 65) f7815 := by
  apply lratCheckerSound f7815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7815
  · intro a ha; simp [p7815] at ha; subst a; trivial
  · exact checked7815
theorem derived7815 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7815 := by
  apply localUnsat_implies_entails f7815 [c7814, c7074, c6782, c7064, c6941] c7815 unsat7815 (by rfl) a
  have h0 : Entails.eval a c7814 := derived7814 a h
  have h1 : Entails.eval a c7074 := h 7073 (by decide)
  have h2 : Entails.eval a c6782 := h 6781 (by decide)
  have h3 : Entails.eval a c7064 := h 7063 (by decide)
  have h4 : Entails.eval a c6941 := h 6940 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7816 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7816 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7807, some c7813, some c7815, some c7074, some c7606, some c6790, some c6945, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7816 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7816 : lratChecker f7816 p7816 = .success := by decide +kernel
theorem unsat7816 : Unsatisfiable (PosFin 65) f7816 := by
  apply lratCheckerSound f7816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7816
  · intro a ha; simp [p7816] at ha; subst a; trivial
  · exact checked7816
theorem derived7816 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7816 := by
  apply localUnsat_implies_entails f7816 [c7712, c7807, c7813, c7815, c7074, c7606, c6790, c6945] c7816 unsat7816 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7807 := derived7807 a h
  have h2 : Entails.eval a c7813 := derived7813 a h
  have h3 : Entails.eval a c7815 := derived7815 a h
  have h4 : Entails.eval a c7074 := h 7073 (by decide)
  have h5 : Entails.eval a c7606 := derived7606 a h
  have h6 : Entails.eval a c6790 := h 6789 (by decide)
  have h7 : Entails.eval a c6945 := h 6944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7817 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨55, by decide⟩, false), (⟨36, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7817 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6945, some c6743, some c6569, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7817 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7817 : lratChecker f7817 p7817 = .success := by decide +kernel
theorem unsat7817 : Unsatisfiable (PosFin 65) f7817 := by
  apply lratCheckerSound f7817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7817
  · intro a ha; simp [p7817] at ha; subst a; trivial
  · exact checked7817
theorem derived7817 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7817 := by
  apply localUnsat_implies_entails f7817 [c6945, c6743, c6569] c7817 unsat7817 (by rfl) a
  have h0 : Entails.eval a c6945 := h 6944 (by decide)
  have h1 : Entails.eval a c6743 := h 6742 (by decide)
  have h2 : Entails.eval a c6569 := h 6568 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7818 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨41, by decide⟩, false), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7818 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6369, some c6546, some c7209, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7818 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7818 : lratChecker f7818 p7818 = .success := by decide +kernel
theorem unsat7818 : Unsatisfiable (PosFin 65) f7818 := by
  apply lratCheckerSound f7818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7818
  · intro a ha; simp [p7818] at ha; subst a; trivial
  · exact checked7818
theorem derived7818 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7818 := by
  apply localUnsat_implies_entails f7818 [c6369, c6546, c7209] c7818 unsat7818 (by rfl) a
  have h0 : Entails.eval a c6369 := h 6368 (by decide)
  have h1 : Entails.eval a c6546 := h 6545 (by decide)
  have h2 : Entails.eval a c7209 := h 7208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7819 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7819 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7807, some c7712, some c7813, some c7815, some c7816, some c7818, some c7817, some c6958, some c6981, some c7118, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7819 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7819 : lratChecker f7819 p7819 = .success := by decide +kernel
theorem unsat7819 : Unsatisfiable (PosFin 65) f7819 := by
  apply lratCheckerSound f7819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7819
  · intro a ha; simp [p7819] at ha; subst a; trivial
  · exact checked7819
theorem derived7819 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7819 := by
  apply localUnsat_implies_entails f7819 [c7807, c7712, c7813, c7815, c7816, c7818, c7817, c6958, c6981, c7118] c7819 unsat7819 (by rfl) a
  have h0 : Entails.eval a c7807 := derived7807 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c7813 := derived7813 a h
  have h3 : Entails.eval a c7815 := derived7815 a h
  have h4 : Entails.eval a c7816 := derived7816 a h
  have h5 : Entails.eval a c7818 := derived7818 a h
  have h6 : Entails.eval a c7817 := derived7817 a h
  have h7 : Entails.eval a c6958 := h 6957 (by decide)
  have h8 : Entails.eval a c6981 := h 6980 (by decide)
  have h9 : Entails.eval a c7118 := h 7117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7820 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7820 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7807, some c7606, some c6966, some c6981, some c7123, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7820 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7820 : lratChecker f7820 p7820 = .success := by decide +kernel
theorem unsat7820 : Unsatisfiable (PosFin 65) f7820 := by
  apply lratCheckerSound f7820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7820
  · intro a ha; simp [p7820] at ha; subst a; trivial
  · exact checked7820
theorem derived7820 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7820 := by
  apply localUnsat_implies_entails f7820 [c7807, c7606, c6966, c6981, c7123] c7820 unsat7820 (by rfl) a
  have h0 : Entails.eval a c7807 := derived7807 a h
  have h1 : Entails.eval a c7606 := derived7606 a h
  have h2 : Entails.eval a c6966 := h 6965 (by decide)
  have h3 : Entails.eval a c6981 := h 6980 (by decide)
  have h4 : Entails.eval a c7123 := h 7122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7821 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7821 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7807, some c7809, some c7820, some c7817, some c6478, some c6382, some c7500, some c7631, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7821 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7821 : lratChecker f7821 p7821 = .success := by decide +kernel
theorem unsat7821 : Unsatisfiable (PosFin 65) f7821 := by
  apply lratCheckerSound f7821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7821
  · intro a ha; simp [p7821] at ha; subst a; trivial
  · exact checked7821
theorem derived7821 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7821 := by
  apply localUnsat_implies_entails f7821 [c7807, c7809, c7820, c7817, c6478, c6382, c7500, c7631] c7821 unsat7821 (by rfl) a
  have h0 : Entails.eval a c7807 := derived7807 a h
  have h1 : Entails.eval a c7809 := derived7809 a h
  have h2 : Entails.eval a c7820 := derived7820 a h
  have h3 : Entails.eval a c7817 := derived7817 a h
  have h4 : Entails.eval a c6478 := h 6477 (by decide)
  have h5 : Entails.eval a c6382 := h 6381 (by decide)
  have h6 : Entails.eval a c7500 := h 7499 (by decide)
  have h7 : Entails.eval a c7631 := derived7631 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7822 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨37, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7822 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7107, some c7075, some c7196, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7822 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7822 : lratChecker f7822 p7822 = .success := by decide +kernel
theorem unsat7822 : Unsatisfiable (PosFin 65) f7822 := by
  apply lratCheckerSound f7822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7822
  · intro a ha; simp [p7822] at ha; subst a; trivial
  · exact checked7822
theorem derived7822 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7822 := by
  apply localUnsat_implies_entails f7822 [c7107, c7075, c7196] c7822 unsat7822 (by rfl) a
  have h0 : Entails.eval a c7107 := h 7106 (by decide)
  have h1 : Entails.eval a c7075 := h 7074 (by decide)
  have h2 : Entails.eval a c7196 := h 7195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7823 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7823 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7822, some c6941, some c6781, some c6770, some c7119, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7823 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7823 : lratChecker f7823 p7823 = .success := by decide +kernel
theorem unsat7823 : Unsatisfiable (PosFin 65) f7823 := by
  apply lratCheckerSound f7823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7823
  · intro a ha; simp [p7823] at ha; subst a; trivial
  · exact checked7823
theorem derived7823 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7823 := by
  apply localUnsat_implies_entails f7823 [c7822, c6941, c6781, c6770, c7119] c7823 unsat7823 (by rfl) a
  have h0 : Entails.eval a c7822 := derived7822 a h
  have h1 : Entails.eval a c6941 := h 6940 (by decide)
  have h2 : Entails.eval a c6781 := h 6780 (by decide)
  have h3 : Entails.eval a c6770 := h 6769 (by decide)
  have h4 : Entails.eval a c7119 := h 7118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7824 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7824 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7823, some c6972, some c6941, some c7546, some c6781, some c6770, some c6948, some c7292, some c7522, some c7541, some c6891, some c7725, some c7794, some c7637, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7824 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7824 : lratChecker f7824 p7824 = .success := by decide +kernel
theorem unsat7824 : Unsatisfiable (PosFin 65) f7824 := by
  apply lratCheckerSound f7824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7824
  · intro a ha; simp [p7824] at ha; subst a; trivial
  · exact checked7824
theorem derived7824 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7824 := by
  apply localUnsat_implies_entails f7824 [c7823, c6972, c6941, c7546, c6781, c6770, c6948, c7292, c7522, c7541, c6891, c7725, c7794, c7637] c7824 unsat7824 (by rfl) a
  have h0 : Entails.eval a c7823 := derived7823 a h
  have h1 : Entails.eval a c6972 := h 6971 (by decide)
  have h2 : Entails.eval a c6941 := h 6940 (by decide)
  have h3 : Entails.eval a c7546 := h 7545 (by decide)
  have h4 : Entails.eval a c6781 := h 6780 (by decide)
  have h5 : Entails.eval a c6770 := h 6769 (by decide)
  have h6 : Entails.eval a c6948 := h 6947 (by decide)
  have h7 : Entails.eval a c7292 := h 7291 (by decide)
  have h8 : Entails.eval a c7522 := h 7521 (by decide)
  have h9 : Entails.eval a c7541 := h 7540 (by decide)
  have h10 : Entails.eval a c6891 := h 6890 (by decide)
  have h11 : Entails.eval a c7725 := derived7725 a h
  have h12 : Entails.eval a c7794 := derived7794 a h
  have h13 : Entails.eval a c7637 := derived7637 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7825 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7825 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7807, some c7712, some c7819, some c7821, some c7824, some c6960, some c7606, some c6977, some c7119, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7825 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7825 : lratChecker f7825 p7825 = .success := by decide +kernel
theorem unsat7825 : Unsatisfiable (PosFin 65) f7825 := by
  apply lratCheckerSound f7825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7825
  · intro a ha; simp [p7825] at ha; subst a; trivial
  · exact checked7825
theorem derived7825 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7825 := by
  apply localUnsat_implies_entails f7825 [c7807, c7712, c7819, c7821, c7824, c6960, c7606, c6977, c7119] c7825 unsat7825 (by rfl) a
  have h0 : Entails.eval a c7807 := derived7807 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c7819 := derived7819 a h
  have h3 : Entails.eval a c7821 := derived7821 a h
  have h4 : Entails.eval a c7824 := derived7824 a h
  have h5 : Entails.eval a c6960 := h 6959 (by decide)
  have h6 : Entails.eval a c7606 := derived7606 a h
  have h7 : Entails.eval a c6977 := h 6976 (by decide)
  have h8 : Entails.eval a c7119 := h 7118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7826 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨50, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7826 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7122, some c7199, some c7191, some c7326, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7826 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7826 : lratChecker f7826 p7826 = .success := by decide +kernel
theorem unsat7826 : Unsatisfiable (PosFin 65) f7826 := by
  apply lratCheckerSound f7826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7826
  · intro a ha; simp [p7826] at ha; subst a; trivial
  · exact checked7826
theorem derived7826 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7826 := by
  apply localUnsat_implies_entails f7826 [c7122, c7199, c7191, c7326] c7826 unsat7826 (by rfl) a
  have h0 : Entails.eval a c7122 := h 7121 (by decide)
  have h1 : Entails.eval a c7199 := h 7198 (by decide)
  have h2 : Entails.eval a c7191 := h 7190 (by decide)
  have h3 : Entails.eval a c7326 := h 7325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7827 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨37, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7827 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7825, some c7807, some c6964, some c7712, some c6319, some c6937, some c6362, some c7731, some c6423, some c7281, some c6943, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7827 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7827 : lratChecker f7827 p7827 = .success := by decide +kernel
theorem unsat7827 : Unsatisfiable (PosFin 65) f7827 := by
  apply lratCheckerSound f7827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7827
  · intro a ha; simp [p7827] at ha; subst a; trivial
  · exact checked7827
theorem derived7827 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7827 := by
  apply localUnsat_implies_entails f7827 [c7825, c7807, c6964, c7712, c6319, c6937, c6362, c7731, c6423, c7281, c6943] c7827 unsat7827 (by rfl) a
  have h0 : Entails.eval a c7825 := derived7825 a h
  have h1 : Entails.eval a c7807 := derived7807 a h
  have h2 : Entails.eval a c6964 := h 6963 (by decide)
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c6319 := h 6318 (by decide)
  have h5 : Entails.eval a c6937 := h 6936 (by decide)
  have h6 : Entails.eval a c6362 := h 6361 (by decide)
  have h7 : Entails.eval a c7731 := derived7731 a h
  have h8 : Entails.eval a c6423 := h 6422 (by decide)
  have h9 : Entails.eval a c7281 := h 7280 (by decide)
  have h10 : Entails.eval a c6943 := h 6942 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7828 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7828 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7825, some c7807, some c6964, some c7827, some c6785, some c6774, some c7294, some c6894, some c7483, some c7494, some c6517, some c6498, some c7793, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7828 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7828 : lratChecker f7828 p7828 = .success := by decide +kernel
theorem unsat7828 : Unsatisfiable (PosFin 65) f7828 := by
  apply lratCheckerSound f7828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7828
  · intro a ha; simp [p7828] at ha; subst a; trivial
  · exact checked7828
theorem derived7828 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7828 := by
  apply localUnsat_implies_entails f7828 [c7825, c7807, c6964, c7827, c6785, c6774, c7294, c6894, c7483, c7494, c6517, c6498, c7793] c7828 unsat7828 (by rfl) a
  have h0 : Entails.eval a c7825 := derived7825 a h
  have h1 : Entails.eval a c7807 := derived7807 a h
  have h2 : Entails.eval a c6964 := h 6963 (by decide)
  have h3 : Entails.eval a c7827 := derived7827 a h
  have h4 : Entails.eval a c6785 := h 6784 (by decide)
  have h5 : Entails.eval a c6774 := h 6773 (by decide)
  have h6 : Entails.eval a c7294 := h 7293 (by decide)
  have h7 : Entails.eval a c6894 := h 6893 (by decide)
  have h8 : Entails.eval a c7483 := h 7482 (by decide)
  have h9 : Entails.eval a c7494 := h 7493 (by decide)
  have h10 : Entails.eval a c6517 := h 6516 (by decide)
  have h11 : Entails.eval a c6498 := h 6497 (by decide)
  have h12 : Entails.eval a c7793 := derived7793 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7829 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7829 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7825, some c7807, some c7826, some c7606, some c6785, some c6319, some c6937, some c7719, some c6423, some c6517, some c7135, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7829 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7829 : lratChecker f7829 p7829 = .success := by decide +kernel
theorem unsat7829 : Unsatisfiable (PosFin 65) f7829 := by
  apply lratCheckerSound f7829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7829
  · intro a ha; simp [p7829] at ha; subst a; trivial
  · exact checked7829
theorem derived7829 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7829 := by
  apply localUnsat_implies_entails f7829 [c7825, c7807, c7826, c7606, c6785, c6319, c6937, c7719, c6423, c6517, c7135] c7829 unsat7829 (by rfl) a
  have h0 : Entails.eval a c7825 := derived7825 a h
  have h1 : Entails.eval a c7807 := derived7807 a h
  have h2 : Entails.eval a c7826 := derived7826 a h
  have h3 : Entails.eval a c7606 := derived7606 a h
  have h4 : Entails.eval a c6785 := h 6784 (by decide)
  have h5 : Entails.eval a c6319 := h 6318 (by decide)
  have h6 : Entails.eval a c6937 := h 6936 (by decide)
  have h7 : Entails.eval a c7719 := derived7719 a h
  have h8 : Entails.eval a c6423 := h 6422 (by decide)
  have h9 : Entails.eval a c6517 := h 6516 (by decide)
  have h10 : Entails.eval a c7135 := h 7134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7830 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7830 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7807, some c7825, some c7829, some c6964, some c7828, some c7817, some c6974, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7830 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7830 : lratChecker f7830 p7830 = .success := by decide +kernel
theorem unsat7830 : Unsatisfiable (PosFin 65) f7830 := by
  apply lratCheckerSound f7830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7830
  · intro a ha; simp [p7830] at ha; subst a; trivial
  · exact checked7830
theorem derived7830 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7830 := by
  apply localUnsat_implies_entails f7830 [c7807, c7825, c7829, c6964, c7828, c7817, c6974] c7830 unsat7830 (by rfl) a
  have h0 : Entails.eval a c7807 := derived7807 a h
  have h1 : Entails.eval a c7825 := derived7825 a h
  have h2 : Entails.eval a c7829 := derived7829 a h
  have h3 : Entails.eval a c6964 := h 6963 (by decide)
  have h4 : Entails.eval a c7828 := derived7828 a h
  have h5 : Entails.eval a c7817 := derived7817 a h
  have h6 : Entails.eval a c6974 := h 6973 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7831 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7831 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7712, some c6612, some c6970, some c6690, some c6298, some c6419, some c6458, some c6652, some c7264, some c7622, some c6794, some c7461, some c7731, some c6868, some c7732, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7831 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7831 : lratChecker f7831 p7831 = .success := by decide +kernel
theorem unsat7831 : Unsatisfiable (PosFin 65) f7831 := by
  apply lratCheckerSound f7831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7831
  · intro a ha; simp [p7831] at ha; subst a; trivial
  · exact checked7831
theorem derived7831 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7831 := by
  apply localUnsat_implies_entails f7831 [c7830, c7712, c6612, c6970, c6690, c6298, c6419, c6458, c6652, c7264, c7622, c6794, c7461, c7731, c6868, c7732] c7831 unsat7831 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c6612 := h 6611 (by decide)
  have h3 : Entails.eval a c6970 := h 6969 (by decide)
  have h4 : Entails.eval a c6690 := h 6689 (by decide)
  have h5 : Entails.eval a c6298 := h 6297 (by decide)
  have h6 : Entails.eval a c6419 := h 6418 (by decide)
  have h7 : Entails.eval a c6458 := h 6457 (by decide)
  have h8 : Entails.eval a c6652 := h 6651 (by decide)
  have h9 : Entails.eval a c7264 := h 7263 (by decide)
  have h10 : Entails.eval a c7622 := derived7622 a h
  have h11 : Entails.eval a c6794 := h 6793 (by decide)
  have h12 : Entails.eval a c7461 := h 7460 (by decide)
  have h13 : Entails.eval a c7731 := derived7731 a h
  have h14 : Entails.eval a c6868 := h 6867 (by decide)
  have h15 : Entails.eval a c7732 := derived7732 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7832 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨59, by decide⟩, false), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7832 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6946, some c6944, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7832 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7832 : lratChecker f7832 p7832 = .success := by decide +kernel
theorem unsat7832 : Unsatisfiable (PosFin 65) f7832 := by
  apply lratCheckerSound f7832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7832
  · intro a ha; simp [p7832] at ha; subst a; trivial
  · exact checked7832
theorem derived7832 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7832 := by
  apply localUnsat_implies_entails f7832 [c6946, c6944] c7832 unsat7832 (by rfl) a
  have h0 : Entails.eval a c6946 := h 6945 (by decide)
  have h1 : Entails.eval a c6944 := h 6943 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7833 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7833 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6888, some c6908, some c7038, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7833 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7833 : lratChecker f7833 p7833 = .success := by decide +kernel
theorem unsat7833 : Unsatisfiable (PosFin 65) f7833 := by
  apply lratCheckerSound f7833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7833
  · intro a ha; simp [p7833] at ha; subst a; trivial
  · exact checked7833
theorem derived7833 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7833 := by
  apply localUnsat_implies_entails f7833 [c6888, c6908, c7038] c7833 unsat7833 (by rfl) a
  have h0 : Entails.eval a c6888 := h 6887 (by decide)
  have h1 : Entails.eval a c6908 := h 6907 (by decide)
  have h2 : Entails.eval a c7038 := h 7037 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7834 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨35, by decide⟩, true), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7834 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7038, some c6690, some c6603, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7834 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7834 : lratChecker f7834 p7834 = .success := by decide +kernel
theorem unsat7834 : Unsatisfiable (PosFin 65) f7834 := by
  apply lratCheckerSound f7834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7834
  · intro a ha; simp [p7834] at ha; subst a; trivial
  · exact checked7834
theorem derived7834 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7834 := by
  apply localUnsat_implies_entails f7834 [c7038, c6690, c6603] c7834 unsat7834 (by rfl) a
  have h0 : Entails.eval a c7038 := h 7037 (by decide)
  have h1 : Entails.eval a c6690 := h 6689 (by decide)
  have h2 : Entails.eval a c6603 := h 6602 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7835 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨50, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7835 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7833, some c7834, some c6832, some c6902, some c7299, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7835 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7835 : lratChecker f7835 p7835 = .success := by decide +kernel
theorem unsat7835 : Unsatisfiable (PosFin 65) f7835 := by
  apply lratCheckerSound f7835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7835
  · intro a ha; simp [p7835] at ha; subst a; trivial
  · exact checked7835
theorem derived7835 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7835 := by
  apply localUnsat_implies_entails f7835 [c7833, c7834, c6832, c6902, c7299] c7835 unsat7835 (by rfl) a
  have h0 : Entails.eval a c7833 := derived7833 a h
  have h1 : Entails.eval a c7834 := derived7834 a h
  have h2 : Entails.eval a c6832 := h 6831 (by decide)
  have h3 : Entails.eval a c6902 := h 6901 (by decide)
  have h4 : Entails.eval a c7299 := h 7298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7836 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨44, by decide⟩, false), (⟨37, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7836 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7832, some c7731, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7836 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7836 : lratChecker f7836 p7836 = .success := by decide +kernel
theorem unsat7836 : Unsatisfiable (PosFin 65) f7836 := by
  apply lratCheckerSound f7836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7836
  · intro a ha; simp [p7836] at ha; subst a; trivial
  · exact checked7836
theorem derived7836 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7836 := by
  apply localUnsat_implies_entails f7836 [c7832, c7731] c7836 unsat7836 (by rfl) a
  have h0 : Entails.eval a c7832 := derived7832 a h
  have h1 : Entails.eval a c7731 := derived7731 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7837 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7837 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7831, some c7830, some c7712, some c7835, some c6327, some c6939, some c7836, some c7729, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7837 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7837 : lratChecker f7837 p7837 = .success := by decide +kernel
theorem unsat7837 : Unsatisfiable (PosFin 65) f7837 := by
  apply lratCheckerSound f7837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7837
  · intro a ha; simp [p7837] at ha; subst a; trivial
  · exact checked7837
theorem derived7837 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7837 := by
  apply localUnsat_implies_entails f7837 [c7831, c7830, c7712, c7835, c6327, c6939, c7836, c7729] c7837 unsat7837 (by rfl) a
  have h0 : Entails.eval a c7831 := derived7831 a h
  have h1 : Entails.eval a c7830 := derived7830 a h
  have h2 : Entails.eval a c7712 := derived7712 a h
  have h3 : Entails.eval a c7835 := derived7835 a h
  have h4 : Entails.eval a c6327 := h 6326 (by decide)
  have h5 : Entails.eval a c6939 := h 6938 (by decide)
  have h6 : Entails.eval a c7836 := derived7836 a h
  have h7 : Entails.eval a c7729 := derived7729 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7838 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨44, by decide⟩, true), (⟨37, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7838 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7440, some c7255, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7838 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7838 : lratChecker f7838 p7838 = .success := by decide +kernel
theorem unsat7838 : Unsatisfiable (PosFin 65) f7838 := by
  apply lratCheckerSound f7838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7838
  · intro a ha; simp [p7838] at ha; subst a; trivial
  · exact checked7838
theorem derived7838 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7838 := by
  apply localUnsat_implies_entails f7838 [c7440, c7255] c7838 unsat7838 (by rfl) a
  have h0 : Entails.eval a c7440 := h 7439 (by decide)
  have h1 : Entails.eval a c7255 := h 7254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7839 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨38, by decide⟩, true), (⟨39, by decide⟩, false), (⟨44, by decide⟩, true), (⟨36, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7839 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7013, some c7345, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7839 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7839 : lratChecker f7839 p7839 = .success := by decide +kernel
theorem unsat7839 : Unsatisfiable (PosFin 65) f7839 := by
  apply lratCheckerSound f7839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7839
  · intro a ha; simp [p7839] at ha; subst a; trivial
  · exact checked7839
theorem derived7839 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7839 := by
  apply localUnsat_implies_entails f7839 [c7013, c7345] c7839 unsat7839 (by rfl) a
  have h0 : Entails.eval a c7013 := h 7012 (by decide)
  have h1 : Entails.eval a c7345 := h 7344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7840 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨48, by decide⟩, true), (⟨55, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7840 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7831, some c7837, some c7157, some c7000, some c6642, some c7223, some c6664, some c7839, some c7789, some c7729, some c6855, some c7553, some c7254, some c6419, some c7790, some c5289, some c5290, some c5499, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7840 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7840 : lratChecker f7840 p7840 = .success := by decide +kernel
theorem unsat7840 : Unsatisfiable (PosFin 65) f7840 := by
  apply lratCheckerSound f7840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7840
  · intro a ha; simp [p7840] at ha; subst a; trivial
  · exact checked7840
theorem derived7840 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7840 := by
  apply localUnsat_implies_entails f7840 [c7830, c7831, c7837, c7157, c7000, c6642, c7223, c6664, c7839, c7789, c7729, c6855, c7553, c7254, c6419, c7790, c5289, c5290, c5499] c7840 unsat7840 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7831 := derived7831 a h
  have h2 : Entails.eval a c7837 := derived7837 a h
  have h3 : Entails.eval a c7157 := h 7156 (by decide)
  have h4 : Entails.eval a c7000 := h 6999 (by decide)
  have h5 : Entails.eval a c6642 := h 6641 (by decide)
  have h6 : Entails.eval a c7223 := h 7222 (by decide)
  have h7 : Entails.eval a c6664 := h 6663 (by decide)
  have h8 : Entails.eval a c7839 := derived7839 a h
  have h9 : Entails.eval a c7789 := derived7789 a h
  have h10 : Entails.eval a c7729 := derived7729 a h
  have h11 : Entails.eval a c6855 := h 6854 (by decide)
  have h12 : Entails.eval a c7553 := derived7553 a h
  have h13 : Entails.eval a c7254 := h 7253 (by decide)
  have h14 : Entails.eval a c6419 := h 6418 (by decide)
  have h15 : Entails.eval a c7790 := derived7790 a h
  have h16 : Entails.eval a c5289 := h 5288 (by decide)
  have h17 : Entails.eval a c5290 := h 5289 (by decide)
  have h18 : Entails.eval a c5499 := h 5498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7841 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨48, by decide⟩, true), (⟨55, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7841 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7831, some c7837, some c7157, some c7000, some c6642, some c7223, some c6664, some c7839, some c7789, some c7729, some c6855, some c7553, some c7254, some c6419, some c5220, some c5289, some c5290, some c6006, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7841 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7841 : lratChecker f7841 p7841 = .success := by decide +kernel
theorem unsat7841 : Unsatisfiable (PosFin 65) f7841 := by
  apply lratCheckerSound f7841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7841
  · intro a ha; simp [p7841] at ha; subst a; trivial
  · exact checked7841
theorem derived7841 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7841 := by
  apply localUnsat_implies_entails f7841 [c7830, c7831, c7837, c7157, c7000, c6642, c7223, c6664, c7839, c7789, c7729, c6855, c7553, c7254, c6419, c5220, c5289, c5290, c6006] c7841 unsat7841 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7831 := derived7831 a h
  have h2 : Entails.eval a c7837 := derived7837 a h
  have h3 : Entails.eval a c7157 := h 7156 (by decide)
  have h4 : Entails.eval a c7000 := h 6999 (by decide)
  have h5 : Entails.eval a c6642 := h 6641 (by decide)
  have h6 : Entails.eval a c7223 := h 7222 (by decide)
  have h7 : Entails.eval a c6664 := h 6663 (by decide)
  have h8 : Entails.eval a c7839 := derived7839 a h
  have h9 : Entails.eval a c7789 := derived7789 a h
  have h10 : Entails.eval a c7729 := derived7729 a h
  have h11 : Entails.eval a c6855 := h 6854 (by decide)
  have h12 : Entails.eval a c7553 := derived7553 a h
  have h13 : Entails.eval a c7254 := h 7253 (by decide)
  have h14 : Entails.eval a c6419 := h 6418 (by decide)
  have h15 : Entails.eval a c5220 := h 5219 (by decide)
  have h16 : Entails.eval a c5289 := h 5288 (by decide)
  have h17 : Entails.eval a c5290 := h 5289 (by decide)
  have h18 : Entails.eval a c6006 := h 6005 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7842 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, true), (⟨57, by decide⟩, false), (⟨45, by decide⟩, true), (⟨41, by decide⟩, false), (⟨40, by decide⟩, false), (⟨35, by decide⟩, true), (⟨38, by decide⟩, true), (⟨46, by decide⟩, false), (⟨34, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7842 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5314, some c5316, some c5276, some c6190, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7842 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7842 : lratChecker f7842 p7842 = .success := by decide +kernel
theorem unsat7842 : Unsatisfiable (PosFin 65) f7842 := by
  apply lratCheckerSound f7842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7842
  · intro a ha; simp [p7842] at ha; subst a; trivial
  · exact checked7842
theorem derived7842 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7842 := by
  apply localUnsat_implies_entails f7842 [c5314, c5316, c5276, c6190] c7842 unsat7842 (by rfl) a
  have h0 : Entails.eval a c5314 := h 5313 (by decide)
  have h1 : Entails.eval a c5316 := h 5315 (by decide)
  have h2 : Entails.eval a c5276 := h 5275 (by decide)
  have h3 : Entails.eval a c6190 := h 6189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7843 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7843 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6006, some c5590, some c5175, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7843 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7843 : lratChecker f7843 p7843 = .success := by decide +kernel
theorem unsat7843 : Unsatisfiable (PosFin 65) f7843 := by
  apply lratCheckerSound f7843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7843
  · intro a ha; simp [p7843] at ha; subst a; trivial
  · exact checked7843
theorem derived7843 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7843 := by
  apply localUnsat_implies_entails f7843 [c6006, c5590, c5175] c7843 unsat7843 (by rfl) a
  have h0 : Entails.eval a c6006 := h 6005 (by decide)
  have h1 : Entails.eval a c5590 := h 5589 (by decide)
  have h2 : Entails.eval a c5175 := h 5174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7844 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨55, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7844 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7837, some c7830, some c7157, some c7831, some c7000, some c7223, some c6642, some c6664, some c7839, some c7838, some c7316, some c7096, some c7789, some c7729, some c6855, some c7833, some c7553, some c6419, some c6387, some c6392, some c7254, some c7840, some c7841, some c7842, some c7843, some c5260, some c5291, some c6133, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7844 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked7844 : lratChecker f7844 p7844 = .success := by decide +kernel
theorem unsat7844 : Unsatisfiable (PosFin 65) f7844 := by
  apply lratCheckerSound f7844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7844
  · intro a ha; simp [p7844] at ha; subst a; trivial
  · exact checked7844
theorem derived7844 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7844 := by
  apply localUnsat_implies_entails f7844 [c7712, c7837, c7830, c7157, c7831, c7000, c7223, c6642, c6664, c7839, c7838, c7316, c7096, c7789, c7729, c6855, c7833, c7553, c6419, c6387, c6392, c7254, c7840, c7841, c7842, c7843, c5260, c5291, c6133] c7844 unsat7844 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7837 := derived7837 a h
  have h2 : Entails.eval a c7830 := derived7830 a h
  have h3 : Entails.eval a c7157 := h 7156 (by decide)
  have h4 : Entails.eval a c7831 := derived7831 a h
  have h5 : Entails.eval a c7000 := h 6999 (by decide)
  have h6 : Entails.eval a c7223 := h 7222 (by decide)
  have h7 : Entails.eval a c6642 := h 6641 (by decide)
  have h8 : Entails.eval a c6664 := h 6663 (by decide)
  have h9 : Entails.eval a c7839 := derived7839 a h
  have h10 : Entails.eval a c7838 := derived7838 a h
  have h11 : Entails.eval a c7316 := h 7315 (by decide)
  have h12 : Entails.eval a c7096 := h 7095 (by decide)
  have h13 : Entails.eval a c7789 := derived7789 a h
  have h14 : Entails.eval a c7729 := derived7729 a h
  have h15 : Entails.eval a c6855 := h 6854 (by decide)
  have h16 : Entails.eval a c7833 := derived7833 a h
  have h17 : Entails.eval a c7553 := derived7553 a h
  have h18 : Entails.eval a c6419 := h 6418 (by decide)
  have h19 : Entails.eval a c6387 := h 6386 (by decide)
  have h20 : Entails.eval a c6392 := h 6391 (by decide)
  have h21 : Entails.eval a c7254 := h 7253 (by decide)
  have h22 : Entails.eval a c7840 := derived7840 a h
  have h23 : Entails.eval a c7841 := derived7841 a h
  have h24 : Entails.eval a c7842 := derived7842 a h
  have h25 : Entails.eval a c7843 := derived7843 a h
  have h26 : Entails.eval a c5260 := h 5259 (by decide)
  have h27 : Entails.eval a c5291 := h 5290 (by decide)
  have h28 : Entails.eval a c6133 := h 6132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7845 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7845 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7844, some c7712, some c7837, some c7830, some c7157, some c7831, some c7000, some c7223, some c6642, some c6664, some c7839, some c7838, some c7789, some c6419, some c7316, some c7729, some c5258, some c5260, some c5292, some c6132, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7845 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7845 : lratChecker f7845 p7845 = .success := by decide +kernel
theorem unsat7845 : Unsatisfiable (PosFin 65) f7845 := by
  apply lratCheckerSound f7845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7845
  · intro a ha; simp [p7845] at ha; subst a; trivial
  · exact checked7845
theorem derived7845 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7845 := by
  apply localUnsat_implies_entails f7845 [c7844, c7712, c7837, c7830, c7157, c7831, c7000, c7223, c6642, c6664, c7839, c7838, c7789, c6419, c7316, c7729, c5258, c5260, c5292, c6132] c7845 unsat7845 (by rfl) a
  have h0 : Entails.eval a c7844 := derived7844 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c7837 := derived7837 a h
  have h3 : Entails.eval a c7830 := derived7830 a h
  have h4 : Entails.eval a c7157 := h 7156 (by decide)
  have h5 : Entails.eval a c7831 := derived7831 a h
  have h6 : Entails.eval a c7000 := h 6999 (by decide)
  have h7 : Entails.eval a c7223 := h 7222 (by decide)
  have h8 : Entails.eval a c6642 := h 6641 (by decide)
  have h9 : Entails.eval a c6664 := h 6663 (by decide)
  have h10 : Entails.eval a c7839 := derived7839 a h
  have h11 : Entails.eval a c7838 := derived7838 a h
  have h12 : Entails.eval a c7789 := derived7789 a h
  have h13 : Entails.eval a c6419 := h 6418 (by decide)
  have h14 : Entails.eval a c7316 := h 7315 (by decide)
  have h15 : Entails.eval a c7729 := derived7729 a h
  have h16 : Entails.eval a c5258 := h 5257 (by decide)
  have h17 : Entails.eval a c5260 := h 5259 (by decide)
  have h18 : Entails.eval a c5292 := h 5291 (by decide)
  have h19 : Entails.eval a c6132 := h 6131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7846 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7846 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7831, some c7837, some c7157, some c7000, some c6642, some c7712, some c7789, some c7223, some c7729, some c6664, some c6855, some c7316, some c6419, some c7553, some c7833, some c7839, some c7838, some c7844, some c7521, some c7426, some c7518, some c7845, some c7843, some c5220, some c5277, some c5233, some c6137, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7846 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked7846 : lratChecker f7846 p7846 = .success := by decide +kernel
theorem unsat7846 : Unsatisfiable (PosFin 65) f7846 := by
  apply lratCheckerSound f7846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7846
  · intro a ha; simp [p7846] at ha; subst a; trivial
  · exact checked7846
theorem derived7846 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7846 := by
  apply localUnsat_implies_entails f7846 [c7830, c7831, c7837, c7157, c7000, c6642, c7712, c7789, c7223, c7729, c6664, c6855, c7316, c6419, c7553, c7833, c7839, c7838, c7844, c7521, c7426, c7518, c7845, c7843, c5220, c5277, c5233, c6137] c7846 unsat7846 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7831 := derived7831 a h
  have h2 : Entails.eval a c7837 := derived7837 a h
  have h3 : Entails.eval a c7157 := h 7156 (by decide)
  have h4 : Entails.eval a c7000 := h 6999 (by decide)
  have h5 : Entails.eval a c6642 := h 6641 (by decide)
  have h6 : Entails.eval a c7712 := derived7712 a h
  have h7 : Entails.eval a c7789 := derived7789 a h
  have h8 : Entails.eval a c7223 := h 7222 (by decide)
  have h9 : Entails.eval a c7729 := derived7729 a h
  have h10 : Entails.eval a c6664 := h 6663 (by decide)
  have h11 : Entails.eval a c6855 := h 6854 (by decide)
  have h12 : Entails.eval a c7316 := h 7315 (by decide)
  have h13 : Entails.eval a c6419 := h 6418 (by decide)
  have h14 : Entails.eval a c7553 := derived7553 a h
  have h15 : Entails.eval a c7833 := derived7833 a h
  have h16 : Entails.eval a c7839 := derived7839 a h
  have h17 : Entails.eval a c7838 := derived7838 a h
  have h18 : Entails.eval a c7844 := derived7844 a h
  have h19 : Entails.eval a c7521 := h 7520 (by decide)
  have h20 : Entails.eval a c7426 := h 7425 (by decide)
  have h21 : Entails.eval a c7518 := h 7517 (by decide)
  have h22 : Entails.eval a c7845 := derived7845 a h
  have h23 : Entails.eval a c7843 := derived7843 a h
  have h24 : Entails.eval a c5220 := h 5219 (by decide)
  have h25 : Entails.eval a c5277 := h 5276 (by decide)
  have h26 : Entails.eval a c5233 := h 5232 (by decide)
  have h27 : Entails.eval a c6137 := h 6136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7847 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7847 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7846, some c7830, some c7831, some c7837, some c7157, some c7000, some c6642, some c7712, some c7013, some c7012, some c7004, some c7015, some c7224, some c6868, some c7277, some c6830, some c6692, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7847 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7847 : lratChecker f7847 p7847 = .success := by decide +kernel
theorem unsat7847 : Unsatisfiable (PosFin 65) f7847 := by
  apply lratCheckerSound f7847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7847
  · intro a ha; simp [p7847] at ha; subst a; trivial
  · exact checked7847
theorem derived7847 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7847 := by
  apply localUnsat_implies_entails f7847 [c7846, c7830, c7831, c7837, c7157, c7000, c6642, c7712, c7013, c7012, c7004, c7015, c7224, c6868, c7277, c6830, c6692] c7847 unsat7847 (by rfl) a
  have h0 : Entails.eval a c7846 := derived7846 a h
  have h1 : Entails.eval a c7830 := derived7830 a h
  have h2 : Entails.eval a c7831 := derived7831 a h
  have h3 : Entails.eval a c7837 := derived7837 a h
  have h4 : Entails.eval a c7157 := h 7156 (by decide)
  have h5 : Entails.eval a c7000 := h 6999 (by decide)
  have h6 : Entails.eval a c6642 := h 6641 (by decide)
  have h7 : Entails.eval a c7712 := derived7712 a h
  have h8 : Entails.eval a c7013 := h 7012 (by decide)
  have h9 : Entails.eval a c7012 := h 7011 (by decide)
  have h10 : Entails.eval a c7004 := h 7003 (by decide)
  have h11 : Entails.eval a c7015 := h 7014 (by decide)
  have h12 : Entails.eval a c7224 := h 7223 (by decide)
  have h13 : Entails.eval a c6868 := h 6867 (by decide)
  have h14 : Entails.eval a c7277 := h 7276 (by decide)
  have h15 : Entails.eval a c6830 := h 6829 (by decide)
  have h16 : Entails.eval a c6692 := h 6691 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7848 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7848 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7712, some c7831, some c7837, some c7157, some c7000, some c7846, some c7847, some c7238, some c7226, some c7248, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7848 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7848 : lratChecker f7848 p7848 = .success := by decide +kernel
theorem unsat7848 : Unsatisfiable (PosFin 65) f7848 := by
  apply lratCheckerSound f7848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7848
  · intro a ha; simp [p7848] at ha; subst a; trivial
  · exact checked7848
theorem derived7848 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7848 := by
  apply localUnsat_implies_entails f7848 [c7830, c7712, c7831, c7837, c7157, c7000, c7846, c7847, c7238, c7226, c7248] c7848 unsat7848 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7712 := derived7712 a h
  have h2 : Entails.eval a c7831 := derived7831 a h
  have h3 : Entails.eval a c7837 := derived7837 a h
  have h4 : Entails.eval a c7157 := h 7156 (by decide)
  have h5 : Entails.eval a c7000 := h 6999 (by decide)
  have h6 : Entails.eval a c7846 := derived7846 a h
  have h7 : Entails.eval a c7847 := derived7847 a h
  have h8 : Entails.eval a c7238 := h 7237 (by decide)
  have h9 : Entails.eval a c7226 := h 7225 (by decide)
  have h10 : Entails.eval a c7248 := h 7247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7849 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨57, by decide⟩, false), (⟨39, by decide⟩, false), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7849 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7848, some c7826, some c7830, some c7712, some c7833, some c7000, some c6826, some c6801, some c6868, some c7801, some c7326, some c6556, some c7797, some c7796, some c434, some c427, some c415, some c2447, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7849 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7849 : lratChecker f7849 p7849 = .success := by decide +kernel
theorem unsat7849 : Unsatisfiable (PosFin 65) f7849 := by
  apply lratCheckerSound f7849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7849
  · intro a ha; simp [p7849] at ha; subst a; trivial
  · exact checked7849
theorem derived7849 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7849 := by
  apply localUnsat_implies_entails f7849 [c7848, c7826, c7830, c7712, c7833, c7000, c6826, c6801, c6868, c7801, c7326, c6556, c7797, c7796, c434, c427, c415, c2447] c7849 unsat7849 (by rfl) a
  have h0 : Entails.eval a c7848 := derived7848 a h
  have h1 : Entails.eval a c7826 := derived7826 a h
  have h2 : Entails.eval a c7830 := derived7830 a h
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c7833 := derived7833 a h
  have h5 : Entails.eval a c7000 := h 6999 (by decide)
  have h6 : Entails.eval a c6826 := h 6825 (by decide)
  have h7 : Entails.eval a c6801 := h 6800 (by decide)
  have h8 : Entails.eval a c6868 := h 6867 (by decide)
  have h9 : Entails.eval a c7801 := derived7801 a h
  have h10 : Entails.eval a c7326 := h 7325 (by decide)
  have h11 : Entails.eval a c6556 := h 6555 (by decide)
  have h12 : Entails.eval a c7797 := derived7797 a h
  have h13 : Entails.eval a c7796 := derived7796 a h
  have h14 : Entails.eval a c434 := h 433 (by decide)
  have h15 : Entails.eval a c427 := h 426 (by decide)
  have h16 : Entails.eval a c415 := h 414 (by decide)
  have h17 : Entails.eval a c2447 := h 2446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7850 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨39, by decide⟩, false), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7850 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7848, some c7826, some c7830, some c7849, some c6794, some c6826, some c6868, some c7109, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7850 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7850 : lratChecker f7850 p7850 = .success := by decide +kernel
theorem unsat7850 : Unsatisfiable (PosFin 65) f7850 := by
  apply lratCheckerSound f7850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7850
  · intro a ha; simp [p7850] at ha; subst a; trivial
  · exact checked7850
theorem derived7850 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7850 := by
  apply localUnsat_implies_entails f7850 [c7848, c7826, c7830, c7849, c6794, c6826, c6868, c7109] c7850 unsat7850 (by rfl) a
  have h0 : Entails.eval a c7848 := derived7848 a h
  have h1 : Entails.eval a c7826 := derived7826 a h
  have h2 : Entails.eval a c7830 := derived7830 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c6794 := h 6793 (by decide)
  have h5 : Entails.eval a c6826 := h 6825 (by decide)
  have h6 : Entails.eval a c6868 := h 6867 (by decide)
  have h7 : Entails.eval a c7109 := h 7108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7850

end CochromaticTwenty.Certificates.FixedCore0
